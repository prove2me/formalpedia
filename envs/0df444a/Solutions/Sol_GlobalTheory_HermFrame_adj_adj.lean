-- Prove2me | solution 1 for GlobalTheory.HermFrame.adj_adj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:41:28.719637+00:00
-- url     : https://prove2.me/submissions/72954ad2-6079-45b2-b6e2-80b5c109c921

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LeTwoMulOfForallScale
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
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
variable [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l]
variable {U : Set E} {H : E → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : E} {k : WithTop ℕ∞}
namespace GlobalTheory.HermFrame
theorem _root_.solution {A : Matrix m m ℂ} {B : Matrix l l ℂ} (hA : A.IsHermitian) (hAu : IsUnit A.det)
    (hB : B.IsHermitian) (hBu : IsUnit B.det) (T : Matrix l m ℂ) : adj B A (adj A B T) = T := by
  have hA' : IsUnit Aᵀ.det := by rwa [det_transpose]
  have hB' : IsUnit Bᵀ.det := by rwa [det_transpose]
  simp only [adj, conjTranspose_mul, conjTranspose_conjTranspose, hB.transpose.eq,
    hA.transpose.inv.eq, Matrix.mul_assoc, nonsing_inv_mul _ hA', Matrix.mul_one,
    nonsing_inv_mul_cancel_left _ _ hB']
end GlobalTheory.HermFrame
