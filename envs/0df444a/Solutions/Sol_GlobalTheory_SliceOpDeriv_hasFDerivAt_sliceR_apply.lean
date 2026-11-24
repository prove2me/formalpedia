-- Prove2me | solution 1 for GlobalTheory.SliceOpDeriv.hasFDerivAt_sliceR_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:17:06.983311+00:00
-- url     : https://prove2.me/submissions/17811045-7ebd-4c82-b92b-af12fed928c0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasTemperateGrowthElim
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ClmSupBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SeminormSliceRLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIteratedFDerivPdLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PartialOperatorFderivFormula
import Theorems.Thm_GlobalTheory_SliceOpDeriv_xPart_apply
import Theorems.Thm_GlobalTheory_SliceOp_clm_sup_bound
import Theorems.Thm_GlobalTheory_SliceSchwartz_sliceR_apply
import Theorems.Thm_GlobalTheory_SliceTaylor_seminorm_slice_taylor_le
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SliceSchwartz.sliceR_apply



set_option autoImplicit false
open GlobalTheory.SliceSchwartz GlobalTheory.SliceOp
open scoped ContDiff
noncomputable section
open GlobalTheory GlobalTheory.SliceOpDeriv
open GlobalTheory.SliceSchwartz GlobalTheory.SliceOp
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {κ κ' κ₁' : Type} [Fintype κ] [Fintype κ'] [Fintype κ₁']
namespace GlobalTheory.SliceOpDeriv
theorem _root_.solution (P : SchwartzMap (κ' → V) ℂ →L[ℂ] SchwartzMap (κ₁' → V) ℂ) (f : SchwartzMap (κ ⊕ κ' → V) ℂ)
    (x : κ → V) (y : κ₁' → V) :
    HasFDerivAt (fun x' => P (sliceR f x') y) (xPart P f x y) x := by
  obtain ⟨s', C, hC, hP⟩ := clm_sup_bound P {((0 : ℕ), (0 : ℕ))}
  set M : ℝ := s'.sup (fun m : ℕ × ℕ => SchwartzMap.seminorm ℂ m.1 (m.2 + 2)) f
  have hM : 0 ≤ M := by positivity
  have hb : ∀ h : κ → V, ‖P (sliceR f (x + h)) y - P (sliceR f x) y - xPart P f x y h‖ ≤ C * M * ‖h‖ ^ 2 := by
    intro h
    set D := sliceR f (x + h) - sliceR f x - sliceR (pd (padL (κ' := κ') h) f) x
    have e : P (sliceR f (x + h)) y - P (sliceR f x) y - xPart P f x y h = P D y := by
      simp only [D, xPart_apply, map_sub, SchwartzMap.sub_apply]
    rw [e]
    have h1 : ‖P D y‖ ≤ ({((0 : ℕ), (0 : ℕ))} : Finset (ℕ × ℕ)).sup (schwartzSeminormFamily ℂ (κ₁' → V) ℂ) (P D) := by
      simpa [schwartzSeminormFamily] using SchwartzMap.norm_le_seminorm ℂ (P D) y
    have h2 : s'.sup (schwartzSeminormFamily ℂ (κ' → V) ℂ) D ≤ ‖h‖ ^ 2 * M := by
      refine Seminorm.finset_sup_apply_le (by positivity) fun i hi => ?_
      refine (GlobalTheory.SliceTaylor.seminorm_slice_taylor_le V κ κ' f i.1 i.2 x h).trans ?_
      gcongr
      exact Seminorm.le_finset_sup_apply (p := fun m : ℕ × ℕ => (SchwartzMap.seminorm ℂ m.1 (m.2 + 2) : Seminorm ℂ (SchwartzMap (κ ⊕ κ' → V) ℂ))) (x := f) hi
    calc ‖P D y‖ ≤ C * s'.sup (schwartzSeminormFamily ℂ (κ' → V) ℂ) D := h1.trans (hP D)
      _ ≤ C * (‖h‖ ^ 2 * M) := mul_le_mul_of_nonneg_left h2 hC
      _ = C * M * ‖h‖ ^ 2 := by ring
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  refine Asymptotics.IsBigO.trans_isLittleO ?_ (Asymptotics.isLittleO_norm_pow_id one_lt_two)
  refine Asymptotics.IsBigO.of_bound (C * M) (Filter.Eventually.of_forall fun h => ?_)
  refine (hb h).trans (le_of_eq ?_)
  rw [Real.norm_of_nonneg (by positivity)]
end GlobalTheory.SliceOpDeriv
