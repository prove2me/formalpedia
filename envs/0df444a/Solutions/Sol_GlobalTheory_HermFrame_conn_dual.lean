-- Prove2me | solution 1 for GlobalTheory.HermFrame.conn_dual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:53:33.614851+00:00
-- url     : https://prove2.me/submissions/15f38892-2cdc-4293-ac59-d6cf4d0d451f

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LeTwoMulOfForallScale
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
import Theorems.Thm_GlobalTheory_HermFrame_mdel_transpose
import Theorems.Thm_GlobalTheory_HermFrame_mdel_inv
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
theorem _root_.solution (h : MContDiffAt 1 H z) (hu : IsUnit (H z).det) (ξ : E) :
    conn (fun x => dualGram (H x)) z ξ = -(conn H z ξ)ᵀ := by
  simp only [dualGram]
  rw [conn, mdel_transpose (fun x => (H x)⁻¹), transpose_transpose, transpose_transpose,
    mdel_inv h hu, nonsing_inv_nonsing_inv _ hu, ← conn_transpose_mul hu, Matrix.mul_neg,
    Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ hu, mul_nonsing_inv_cancel_right _ _ hu]
end GlobalTheory.HermFrame
