-- Prove2me | solution 1 for Nock.Verb.next_hintProg_none
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:22:54.244204+00:00
-- url     : https://prove2.me/submissions/2122c46f-6b02-4f36-a467-46b47e40e5ba

module
public import Definitions.Def_LeanPool_PureNock_Agreement
public import Definitions.Def_LeanPool_PureNock_Trace
public import Definitions.Def_LeanPool_PureNock_PaperReference
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureAgreement
public import Theorems.Thm_Nock_Verb_star_pending_is_root
public import Theorems.Thm_Nock_Verb_next_eq_some_iff
public import Theorems.Thm_Nock_Verb_ofNoun_terminal


set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution (subj n2 : Noun) :
    next (program subj (.cell (.atom 11) n2)) = none := by
  cases hb : next (program subj (.cell (.atom 11) n2)) with
  | none => rfl
  | some b =>
      exfalso
      obtain ⟨i, sub, r, hmax, hmap, hdom, _, _⟩ := next_eq_some_iff.1 hb
      obtain ⟨w, hmapw, hpw⟩ := hmax.1
      have hsw : sub = w := Option.some.inj (hmap.symm.trans hmapw)
      have hpsub : sub.isPending = true := hsw ▸ hpw
      have hL : isTerminal (ofNoun subj) = true := ofNoun_terminal subj
      have hR : isTerminal (ofNoun (.cell (.atom 11) n2)) = true := ofNoun_terminal _
      have hroot : sub = .node .star (ofNoun subj) (ofNoun (.cell (.atom 11) n2)) :=
        star_pending_is_root hL hR (by simpa [program] using hmap) hpsub
      rw [hroot] at hdom
      simp [inDomain, inOpcodeDomain, opReady, ofNoun, opHeadOk, Action.isOperator,
        Action.isNull, isTerminal] at hdom
end Nock.Verb
