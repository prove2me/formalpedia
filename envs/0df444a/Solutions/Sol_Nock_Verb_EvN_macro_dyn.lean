-- Prove2me | solution 1 for Nock.Verb.EvN_macro_dyn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:22:25.921059+00:00
-- url     : https://prove2.me/submissions/ebbff94e-3fa2-4a92-80ef-74d24ab8e709

module
public import Definitions.Def_LeanPool_PureNock_Agreement
public import Definitions.Def_LeanPool_PureNock_Trace
public import Definitions.Def_LeanPool_PureNock_PaperReference
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureAgreement
public import Theorems.Thm_Nock_Verb_EvN_op0
public import Theorems.Thm_Nock_Verb_EvN_op7
public import Theorems.Thm_Nock_Verb_EvN_op8
public import Theorems.Thm_Nock_Verb_slot_three


set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {subj clue body x} :
    Ev subj (.cell (.atom 8)
        (.cell clue (.cell (.atom 7) (.cell (.cell (.atom 0) (.atom 3)) body)))) x ↔
      (∃ cv, Ev subj clue cv) ∧ Ev subj body x := by
  rw [EvN_op8]
  constructor
  · rintro ⟨hb, hc, sb, heq, hclue, hrest⟩
    obtain ⟨rfl, rfl⟩ := Noun.cell.inj heq
    rw [EvN_op7] at hrest
    obtain ⟨hb2, hc2, sb2, heq2, hslot, hbody⟩ := hrest
    obtain ⟨rfl, rfl⟩ := Noun.cell.inj heq2
    rw [EvN_op0] at hslot
    obtain ⟨ax, hax, hs⟩ := hslot
    obtain rfl := Noun.atom.inj hax
    rw [slot_three] at hs
    obtain rfl := Option.some.inj hs
    exact ⟨⟨sb, hclue⟩, hbody⟩
  · rintro ⟨⟨cv, hclue⟩, hbody⟩
    refine ⟨clue, _, cv, rfl, hclue, ?_⟩
    rw [EvN_op7]
    refine ⟨.cell (.atom 0) (.atom 3), body, subj, rfl, ?_, hbody⟩
    rw [EvN_op0]
    exact ⟨3, rfl, slot_three⟩
end Nock.Verb
