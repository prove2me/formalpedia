-- Prove2me | solution 1 for GlobalTheory.FubiniStudyHessian.wd_coord
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:00:47.475432+00:00
-- url     : https://prove2.me/submissions/b1a4719b-6b7c-4377-972e-55093f4a51c3

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EventuallyDifferentiableAtOfContDiffAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ComplexHessianLogOneAddNormSq
import Theorems.Thm_GlobalTheory_FubiniStudyHessian_differentiableAt_coord
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wd_of_differentiableAt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.FubiniStudyHessian
open ReciprocityTheory.L2DbarEstimates
open scoped ComplexConjugate
variable {n : ℕ}
namespace GlobalTheory.FubiniStudyHessian
theorem _root_.solution (j i : Fin n) (x : V n) : wd n j (fun w : V n => w i) x = if j = i then 1 else 0 := by
  rw [wd_of_differentiableAt (differentiableAt_coord i x)]
  have h : fderiv ℂ (fun w : V n => w i) x = EuclideanSpace.proj (𝕜 := ℂ) i :=
    (EuclideanSpace.proj (𝕜 := ℂ) i).fderiv
  rw [h]
  by_cases hji : j = i
  · subst hji; simp [bas]
  · simp [bas, hji, Ne.symm hji]
end GlobalTheory.FubiniStudyHessian
