-- Prove2me | solution 1 for GlobalTheory.SliceOp.clm_sup_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:25:02.910399+00:00
-- url     : https://prove2.me/submissions/de73c81d-dc33-41e2-9f9f-e552e7bc2aa7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasTemperateGrowthElim
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ClmSupBound
import Theorems.Thm_GlobalTheory_SliceSchwartz_sliceR_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SliceSchwartz.sliceR_apply



set_option autoImplicit false
open GlobalTheory.SliceSchwartz
open scoped ContDiff
noncomputable section
open GlobalTheory GlobalTheory.SliceOp
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
namespace GlobalTheory.SliceOp
theorem _root_.solution {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (T : SchwartzMap X ℂ →L[ℂ] SchwartzMap Y ℂ) (s : Finset (ℕ × ℕ)) :
    ∃ (s' : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧ ∀ f : SchwartzMap X ℂ,
      s.sup (schwartzSeminormFamily ℂ Y ℂ) (T f) ≤ C * s'.sup (schwartzSeminormFamily ℂ X ℂ) f := by
  have hp : Continuous ((s.sup (schwartzSeminormFamily ℂ Y ℂ)).comp T.toLinearMap) :=
    (Seminorm.continuous_finsetSup fun i _ => (schwartz_withSeminorms ℂ Y ℂ).continuous_seminorm i).comp
      T.continuous
  obtain ⟨s', C, -, hC⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ X ℂ) _ hp
  refine ⟨s', C, C.2, fun f => ?_⟩
  have := hC f
  simpa [Seminorm.smul_apply, NNReal.smul_def] using this
end GlobalTheory.SliceOp
