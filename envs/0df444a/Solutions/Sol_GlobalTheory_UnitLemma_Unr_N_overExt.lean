-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Unr.N_overExt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:21:18.22116+00:00
-- url     : https://prove2.me/submissions/8fa386ef-ec10-47a7-82ce-6b95fa611457

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MemRangeOfValNonneg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WeightedOrbitSumCongrCoefficientRingStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsIntegralUnramifiedExtIffIsIntegralBaseStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HermitianDualInvAlgBaseChangeUnramifiedIffStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsFullLatticeOverUnramifiedExtIffStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedBaseChangeLatticeCountEq
import Theorems.Thm_GlobalTheory_T_hermitianDual_invAlgBaseChangeUnramified_iff
import Theorems.Thm_GlobalTheory_T_isFullLatticeOver_unramifiedExt_iff
import Theorems.Thm_GlobalTheory_T_isIntegral_unramifiedExt_iff_isIntegral_base
import Theorems.Thm_GlobalTheory_T_weightedOrbitSum_congr_coefficientRing
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_exists_int_image


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr
open GlobalTheory.UnitLemma Polynomial
namespace GlobalTheory.UnitLemma.Unr
theorem _root_.solution : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∀ (B : InvAlg K) (ψ : K'.E →+* B.A) (hψ : ∀ e, ψ (φ e) = algebraMap K.E B.A e) (hσ : ∀ e, B.σ (ψ e) = ψ (K'.c e)), (∀ y : K'.O, ψ (algebraMap K'.O K'.E y) ∈ Algebra.adjoin K.O ({B.g} : Set B.A)) → ∀ x : B.A, (overExt φ B ψ hψ hσ).N x = B.N x := by
  intro K K' d φ hU B ψ hψ hσ hO x
  refine (@GlobalTheory.T.weightedOrbitSum_congr_coefficientRing K.O K'.O B.A _ _ B.cA B.aO (overExt φ B ψ hψ hσ).aO B.T (B.X x) ((overExt φ B ψ hψ hσ).X x) ?_ ?_ ?_)
  · intro L hL
    let S : Subalgebra K.O B.A :=
      { carrier := {a | ∀ z ∈ L, a * z ∈ L}
        mul_mem' := fun {a b} ha hb z hz => by rw [mul_assoc]; exact ha _ (hb z hz)
        add_mem' := fun {a b} ha hb z hz => by rw [add_mul]; exact L.add_mem (ha z hz) (hb z hz)
        algebraMap_mem' := fun c z hz => by rw [← Algebra.smul_def]; exact L.smul_mem c hz }
    have hS : Algebra.adjoin K.O ({B.g} : Set B.A) ≤ S := by
      rw [Algebra.adjoin_le_iff, Set.singleton_subset_iff]
      exact fun z hz => hL.2.1 z hz
    let L' : Submodule K'.O (overExt φ B ψ hψ hσ).A :=
      { carrier := (L : Set B.A)
        add_mem' := fun ha hb => L.add_mem ha hb
        zero_mem' := L.zero_mem
        smul_mem' := fun c z hz => hS (hO c) z hz }
    refine ⟨L', ⟨(GlobalTheory.T.isFullLatticeOver_unramifiedExt_iff K K' d φ hU B ψ hψ hσ L' L rfl).2 hL.1, fun y hy => hL.2.1 y hy, fun y => ?_⟩, rfl⟩
    exact (hL.2.2 y).trans (GlobalTheory.T.hermitianDual_invAlgBaseChangeUnramified_iff K K' d φ hU B ψ hψ hσ L' x y).symm
  · intro L' hL'
    let M : Submodule K.O B.A :=
      { carrier := (L' : Set B.A)
        add_mem' := fun ha hb => L'.add_mem ha hb
        zero_mem' := L'.zero_mem
        smul_mem' := fun c z hz => by
          obtain ⟨b, hb⟩ := exists_int_image hU c
          have h : c • z = ψ (algebraMap K'.O K'.E b) * z := by
            rw [Algebra.smul_def, hb, hψ, ← IsScalarTower.algebraMap_apply]
          rw [h]; exact L'.smul_mem b hz }
    refine ⟨M, ⟨(GlobalTheory.T.isFullLatticeOver_unramifiedExt_iff K K' d φ hU B ψ hψ hσ L' M rfl).1 hL'.1, fun y hy => hL'.2.1 y hy, fun y => ?_⟩, rfl⟩
    exact (hL'.2.2 y).trans (GlobalTheory.T.hermitianDual_invAlgBaseChangeUnramified_iff K K' d φ hU B ψ hψ hσ L' x y)
  · ext t
    simp only [Subgroup.mem_inf]
    refine and_congr_left' ?_
    change (IsIntegral K.O (t : B.A) ∧ IsIntegral K.O ((t⁻¹ : B.Aˣ) : B.A)) ↔
      (@IsIntegral K'.O (overExt φ B ψ hψ hσ).A _ _ _ (t : B.A) ∧ @IsIntegral K'.O (overExt φ B ψ hψ hσ).A _ _ _ ((t⁻¹ : B.Aˣ) : B.A))
    rw [GlobalTheory.T.isIntegral_unramifiedExt_iff_isIntegral_base K K' d φ hU B ψ hψ hσ, GlobalTheory.T.isIntegral_unramifiedExt_iff_isIntegral_base K K' d φ hU B ψ hψ hσ]
end GlobalTheory.UnitLemma.Unr
