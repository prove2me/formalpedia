-- Prove2me | solution 1 for MatchingLogic.locConsistent_extend_freshWitnessed_isMCS_unrestricted_refuted
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:44:48.282686+00:00
-- url     : https://prove2.me/submissions/56caf1ca-da9a-43d5-b0fc-737d20c78917

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_WitnessedCollapse
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Lindenbaum
public import Mathlib.Data.Set.Finite.Basic
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_WitnessSupply
public import Theorems.Thm_MatchingLogic_LocProvable_mp
public import Theorems.Thm_MatchingLogic_witnessCollapseTheory_isMCS
public import Theorems.Thm_MatchingLogic_witnessCollapseTheory_not_freshWitnessed


set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open Set
variable {S : Signature}
noncomputable section
attribute [local instance] MatchingLogic.witnessSupplyDecidableEqPattern
namespace MatchingLogic
theorem _root_.solution :
    ¬ (∀ {Gamma : Set (Pattern WitnessCollapseSig Nat)},
      LocConsistent Gamma →
        ∃ Delta : Set (Pattern WitnessCollapseSig Nat),
          Gamma ⊆ Delta ∧ IsMCS Delta ∧ FreshWitnessed Delta) := by
  intro hExtension
  obtain ⟨Delta, hsub, hDeltaMCS, hDeltaFresh⟩ :=
    hExtension witnessCollapseTheory_isMCS.1
  have hEq : Delta = witnessCollapseTheory := by
    apply Set.Subset.antisymm _ hsub
    by_contra hnotSubset
    obtain ⟨p, hpDelta, hpNotTheory⟩ := Set.not_subset.mp hnotSubset
    have hstrict : witnessCollapseTheory ⊂ Delta :=
      (Set.ssubset_iff_of_subset hsub).mpr ⟨p, hpDelta, hpNotTheory⟩
    exact (witnessCollapseTheory_isMCS.2 hstrict) hDeltaMCS.1
  rw [hEq] at hDeltaFresh
  exact witnessCollapseTheory_not_freshWitnessed hDeltaFresh
end MatchingLogic
