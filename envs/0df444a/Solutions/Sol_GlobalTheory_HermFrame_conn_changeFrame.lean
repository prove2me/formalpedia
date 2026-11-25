-- Prove2me | solution 1 for GlobalTheory.HermFrame.conn_changeFrame
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:49:45.823678+00:00
-- url     : https://prove2.me/submissions/2b590394-b49f-4c7b-b2ed-23580912f5e5

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LeTwoMulOfForallScale
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
import Theorems.Thm_GlobalTheory_HermFrame_mdel_transpose
import Theorems.Thm_GlobalTheory_HermFrame_mdel_conjTranspose
import Theorems.Thm_GlobalTheory_HermFrame_MContDiffAt_conjTranspose
import Theorems.Thm_GlobalTheory_HermFrame_mdel_mul
import Theorems.Thm_GlobalTheory_HermFrame_opNorm_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.HermFrame.opNorm_zero



set_option autoImplicit false
open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
noncomputable section
open GlobalTheory GlobalTheory.HermFrame
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E]
variable {m n l : Type*}
variable [Fintype n] [DecidableEq n]
variable {U : Set E} {H H' : E → Matrix n n ℂ} {z : E} {j k : WithTop ℕ∞}
namespace GlobalTheory.HermFrame
theorem _root_.solution {A : E → Matrix n n ℂ} (h : MContDiffAt 1 H z) (hu : IsUnit (H z).det)
    (hA : MContDiffAt 1 A z) (hAu : IsUnit (A z).det) (hA0 : ∀ η, mdbar A z η = 0) (ξ : E) :
    conn (fun x => (A x)ᵀ * H x * (A x)ᴴᵀ) z ξ =
      (A z)⁻¹ * (conn H z ξ * A z + mdel A z ξ) := by
  refine (eq_conn_of_compatible ?_ ?_).symm
  · simp only [det_mul, det_transpose, det_conjTranspose]
    exact (hAu.mul hu).mul hAu.star
  · rw [mdel_mul (hA.transpose.mul h) hA.conjTranspose.transpose, mdel_mul hA.transpose h,
      mdel_transpose (fun x => (A x)ᴴ), mdel_conjTranspose, hA0, ← conn_transpose_mul hu,
      mdel_transpose, transpose_mul, transpose_nonsing_inv]
    simp only [Matrix.mul_assoc, nonsing_inv_mul_cancel_left _ _ (by rwa [det_transpose] :
      IsUnit (A z)ᵀ.det), transpose_add, transpose_mul, Matrix.add_mul, conjTranspose_zero,
      transpose_zero, Matrix.mul_zero, zero_add]
end GlobalTheory.HermFrame
