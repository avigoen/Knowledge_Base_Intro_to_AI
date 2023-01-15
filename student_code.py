import read
import copy
from util import *
from logical_classes import *

verbose = 0


class KnowledgeBase(object):
    def __init__(self, facts=[], rules=[]):
        self.facts = facts
        self.rules = rules
        self.ie = InferenceEngine()

    def __repr__(self):
        return 'KnowledgeBase({!r}, {!r})'.format(self.facts, self.rules)

    def __str__(self):
        string = "Knowledge Base: \n"
        string += "\n".join((str(fact) for fact in self.facts)) + "\n"
        string += "\n".join((str(rule) for rule in self.rules))
        return string

    def _get_fact(self, fact):
        """INTERNAL USE ONLY
        Get the fact in the KB that is the same as the fact argument

        Args:
            fact (Fact): Fact we're searching for

        Returns:
            Fact: matching fact
        """
        for kbfact in self.facts:
            if fact == kbfact:
                return kbfact

    def _get_rule(self, rule):
        """INTERNAL USE ONLY
        Get the rule in the KB that is the same as the rule argument

        Args:
            rule (Rule): Rule we're searching for

        Returns:
            Rule: matching rule
        """
        for kbrule in self.rules:
            if rule == kbrule:
                return kbrule

    def _remove_rule(self, rule):
        """INTERNAL USE ONLY
        Remove the rule in the KB that is the same as the rule argument

        Args:
            rule (Rule): Rule we're removing

        Returns:
            None
        """
        self.rules.remove(rule)

    def _remove_fact(self, fact):
        """INTERNAL USE ONLY
        Remove the fact in the KB that is the same as the fact argument

        Args:
            fact (Fact): Fact we're removing

        Returns:
            None
        """
        self.facts.remove(fact)

    def kb_add(self, fact_rule):
        """Add a fact or rule to the KB
        Args:
            fact_rule (Fact or Rule) - Fact or Rule to be added
        Returns:
            None
        """
        printv("Adding {!r}", 1, verbose, [fact_rule])
        if isinstance(fact_rule, Fact):
            if fact_rule not in self.facts:
                self.facts.append(fact_rule)
                for rule in self.rules:
                    self.ie.fc_infer(fact_rule, rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.facts.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.facts[ind].supported_by.append(f)
                else:
                    ind = self.facts.index(fact_rule)
                    self.facts[ind].asserted = True
        elif isinstance(fact_rule, Rule):
            if fact_rule not in self.rules:
                self.rules.append(fact_rule)
                for fact in self.facts:
                    self.ie.fc_infer(fact, fact_rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.rules.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.rules[ind].supported_by.append(f)
                else:
                    ind = self.rules.index(fact_rule)
                    self.rules[ind].asserted = True

    def kb_assert(self, fact_rule):
        """Assert a fact or rule into the KB

        Args:
            fact_rule (Fact or Rule): Fact or Rule we're asserting
        """
        printv("Asserting {!r}", 0, verbose, [fact_rule])
        self.kb_add(fact_rule)

    def kb_ask(self, fact):
        """Ask if a fact is in the KB

        Args:
            fact (Fact) - Statement to be asked (will be converted into a Fact)

        Returns:
            listof Bindings|False - list of Bindings if result found, False otherwise
        """
        print("Asking {!r}".format(fact))
        if factq(fact):
            f = Fact(fact.statement)
            bindings_lst = ListOfBindings()
            # ask matched facts
            for fact in self.facts:
                binding = match(f.statement, fact.statement)
                if binding:
                    bindings_lst.add_bindings(binding, [fact])

            return bindings_lst if bindings_lst.list_of_bindings else []

        else:
            print("Invalid ask:", fact.statement)
            return []

    def supported_by_remove_fact(self, fact, fact_or_rule):
        """Remove the fact_or_rule from the fact supports and try to retract the fact if it is not asserted

        Args:
            fact (Fact) - Fact to be retracted
            fact_or_rule (Fact or Rule) - Fact or Rule which needs to be checked against the Fact Supports

        Returns:
            None
        """

        for rule_fact_supported in fact.supported_by:
            if fact_or_rule in rule_fact_supported:
                fact.supported_by.remove(rule_fact_supported)

        if not fact.asserted:
            self.kb_retract(fact)

    def supported_by_remove_rule(self, rule, fact_or_rule):
        """Remove the fact_or_rule from the rule supports and try to retract the rule if it is not asserted

        Args:
            rule (Rule) - Rule to be retracted
            fact_or_rule (Fact or Rule) - Fact or Rule which needs to be checked against the Rule Supports

        Returns:
            None
        """

        for rule_fact_supported in rule.supported_by:
            if fact_or_rule in rule_fact_supported:
                rule.supported_by.remove(rule_fact_supported)

        if not fact_or_rule.asserted:
            self.kb_retract(rule)

    def remove_fact(self, fact):
        """Retract a fact from the KB

        Args:
            fact (Fact) - Fact to be retracted

        Returns:
            None
        """

        if fact.supported_by:
            return

        if fact.asserted:
            fact.asserted = False

        for supported_fact in fact.supports_facts:
            self.supported_by_remove_fact(supported_fact, fact)

        for supported_rule in fact.supports_rules:
            self.supported_by_remove_rule(supported_rule, fact)

        self._remove_fact(fact)

    def remove_rule(self, rule):
        """Retract a rule from the KB

        Args:
            rule (Rule) - Rule to be retracted

        Returns:
            None
        """

        if rule.supported_by or rule.asserted:
            return

        for fact in rule.supports_facts:
            self.supported_by_remove_fact(fact, rule)

        for rule_supported in rule.supports_rules:
            self.supported_by_remove_rule(rule_supported, rule)

        self._remove_rule(rule)

    def kb_retract(self, fact_rule):
        """Retract a fact or a rule from the KB

        Args:
            fact_rule (Fact or Rule) - Fact or Rule to be retracted

        Returns:
            None
        """
        printv("Retracting {!r}", 0, verbose, [fact_rule])
        ####################################################
        # Student code goes here
        if isinstance(fact_rule, Fact):
            if fact_rule not in self.facts:
                return
            fact = self._get_fact(fact_rule)
            self.remove_fact(fact)
        elif isinstance(fact_rule, Rule):
            if fact_rule not in self.rules:
                return
            rule = self._get_rule(fact_rule)
            self.remove_rule(rule)


class InferenceEngine(object):
    def fc_infer(self, fact, rule, kb):
        """Forward-chaining to infer new facts and rules

        Args:
            fact (Fact) - A fact from the KnowledgeBase
            rule (Rule) - A rule from the KnowledgeBase
            kb (KnowledgeBase) - A KnowledgeBase

        Returns:
            Nothing
        """
        printv('Attempting to infer from {!r} and {!r} => {!r}', 1, verbose,
               [fact.statement, rule.lhs, rule.rhs])
        ####################################################
        # Student code goes here
        bindings = match(fact.statement, rule.lhs[0])
        if not bindings:
            return

        if len(rule.lhs) == 1:
            new_fact = Fact(instantiate(rule.rhs, bindings), [[fact, rule]])
            fact.supports_facts.append(new_fact)
            rule.supports_facts.append(new_fact)
            kb.kb_add(new_fact)
        else:
            new_rule = Rule([[instantiate(rule_lhs, bindings) for rule_lhs in rule.lhs[1:]], instantiate(
                rule.rhs, bindings)], [[fact, rule]])
            fact.supports_rules.append(new_rule)
            rule.supports_rules.append(new_rule)
            kb.kb_add(new_rule)
