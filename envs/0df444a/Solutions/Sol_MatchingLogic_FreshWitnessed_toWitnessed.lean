-- Prove2me | solution 1 for MatchingLogic.FreshWitnessed.toWitnessed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:24:43.65721+00:00
-- url     : https://prove2.me/submissions/e34a15d7-23f1-4271-8852-cac0e3159711

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CaptureAvoiding
public import Mathlib.Data.Countable.Defs
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_LocalTheory
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Alpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Lindenbaum
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Witnessed

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open Set
variable {S : Signature}
noncomputable section
attribute [local instance] MatchingLogic.instDecidableEqPatternNatWitnessed
namespace MatchingLogic
namespace FreshWitnessed
theorem _root_.solution {Gamma : Set (Pattern S Nat)}
    (h : FreshWitnessed Gamma) : Witnessed Gamma := by
  intro x p hex
  obtain ⟨y, _hyfresh, hy⟩ := h hex
  exact ⟨y, hy⟩
end FreshWitnessed
end MatchingLogic
