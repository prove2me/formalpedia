-- Prove2me | solution 1 for GlobalTheory.DualNumberLocal.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:44:31.9449+00:00
-- url     : https://prove2.me/submissions/13df9f7e-4185-4afe-bd40-c17114c5956e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ImportsRest
import Theorems.Thm_GlobalTheory_FormalIsogeny_isAdicComplete_maximalIdeal_of_finite
import Theorems.Thm_GlobalTheory_constDerivEval_X
import Theorems.Thm_GlobalTheory_mvEvalAdic_C
import Theorems.Thm_GlobalTheory_mvEvalAdic_X
import Theorems.Thm_GlobalTheory_mvEvalAdic_coe
import Theorems.Thm_GlobalTheory_pderivEval_X
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.constDerivEval_X
attribute [local simp] GlobalTheory.mvEvalAdic_C
attribute [local simp] GlobalTheory.mvEvalAdic_X
attribute [local simp] GlobalTheory.mvEvalAdic_coe
attribute [local simp] GlobalTheory.pderivEval_X



set_option autoImplicit false
open IsLocalRing Matrix
open GlobalTheory GlobalTheory.DualNumberLocal
namespace GlobalTheory.DualNumberLocal
theorem _root_.solution : ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O], ∃ _ : IsLocalRing (DualNumber O), IsNoetherianRing (DualNumber O) ∧ IsAdicComplete (maximalIdeal (DualNumber O)) (DualNumber O) ∧ IsLocalHom (algebraMap O (DualNumber O)) ∧ Function.Surjective (fun x : O => residue (DualNumber O) (algebraMap O (DualNumber O) x)) ∧ ∀ z : DualNumber O, z ∈ maximalIdeal (DualNumber O) ↔ z.fst ∈ maximalIdeal O := by
  intro O _ _ _ _
  haveI hloc : IsLocalRing (DualNumber O) :=
    IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
      simp only [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_one]
      exact isUnit_or_isUnit_one_sub_self _
  haveI : Module.Finite O (DualNumber O) := inferInstanceAs (Module.Finite O (O × O))
  have hmem : ∀ z : DualNumber O, z ∈ maximalIdeal (DualNumber O) ↔ z.fst ∈ maximalIdeal O := by
    intro z
    rw [IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      mem_nonunits_iff, TrivSqZeroExt.isUnit_iff_isUnit_fst]
  refine ⟨hloc, IsNoetherianRing.of_finite O (DualNumber O),
    GlobalTheory.FormalIsogeny.isAdicComplete_maximalIdeal_of_finite O (DualNumber O), ?_, ?_, hmem⟩
  · refine ⟨fun a h => ?_⟩
    rw [TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.isUnit_iff_isUnit_fst,
      TrivSqZeroExt.fst_inl] at h
    exact h
  · intro y
    obtain ⟨z, rfl⟩ := IsLocalRing.residue_surjective y
    refine ⟨z.fst, ?_⟩
    show residue (DualNumber O) (algebraMap O (DualNumber O) z.fst) = residue (DualNumber O) z
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, hmem,
      TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_inl, sub_self]
    exact Ideal.zero_mem _
end GlobalTheory.DualNumberLocal
