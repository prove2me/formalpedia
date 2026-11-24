-- Prove2me | solution 1 for GlobalTheory.FubiniStudyHessian.wd_normSq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:04:52.821503+00:00
-- url     : https://prove2.me/submissions/8947a30d-cb72-4db4-ad25-d57dbec91d43

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EventuallyDifferentiableAtOfContDiffAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ComplexHessianLogOneAddNormSq
import Theorems.Thm_GlobalTheory_FubiniStudyHessian_differentiableAt_coord
import Theorems.Thm_GlobalTheory_FubiniStudyHessian_wd_coord
import Theorems.Thm_GlobalTheory_FubiniStudyHessian_normSq_eq_sum
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_differentiableAt_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wd_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wd_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wd_sum
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wdb_of_differentiableAt


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
theorem _root_.solution (j : Fin n) (x : V n) :
    wd n j (fun w : V n => ((‖w‖ ^ 2 : ℝ) : ℂ)) x = conj (x j) := by
  have hd : ∀ i, DifferentiableAt ℝ (fun w : V n => w i) x := fun i =>
    (differentiableAt_coord i x).restrictScalars ℝ
  rw [normSq_eq_sum, wd_sum Finset.univ (f := fun i (w : V n) => w i * conj (w i))
    (fun i _ => (hd i).mul (differentiableAt_conj (hd i)))]
  have h : ∀ i, wd n j (fun w : V n => w i * conj (w i)) x = if j = i then conj (x i) else 0 := fun i => by
    rw [wd_mul (hd i) (differentiableAt_conj (hd i)), wd_conj (hd i),
      wdb_of_differentiableAt (differentiableAt_coord i x), wd_coord]
    simp
  simp [h]
end GlobalTheory.FubiniStudyHessian
