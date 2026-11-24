-- Prove2me | solution 1 for GlobalTheory.FubiniStudyHessian.wdb_normSq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:31:14.265228+00:00
-- url     : https://prove2.me/submissions/f058ba94-8772-4677-80f9-c2d8f51bd8da

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EventuallyDifferentiableAtOfContDiffAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ComplexHessianLogOneAddNormSq
import Theorems.Thm_GlobalTheory_FubiniStudyHessian_differentiableAt_normSq
import Theorems.Thm_GlobalTheory_FubiniStudyHessian_wd_normSq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wdb_ofReal


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
    wdb n j (fun w : V n => ((‖w‖ ^ 2 : ℝ) : ℂ)) x = x j := by
  rw [wdb_ofReal (differentiableAt_normSq x), wd_normSq, Complex.conj_conj]
end GlobalTheory.FubiniStudyHessian
