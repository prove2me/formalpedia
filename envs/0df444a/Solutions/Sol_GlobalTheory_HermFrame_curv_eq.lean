-- Prove2me | solution 1 for GlobalTheory.HermFrame.curv_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:54:28.333896+00:00
-- url     : https://prove2.me/submissions/4c7e3f2d-1cdd-4a10-aa97-f4a075ab8ef8

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LeTwoMulOfForallScale
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
import Theorems.Thm_GlobalTheory_HermFrame_mdbar_transpose
import Theorems.Thm_GlobalTheory_HermFrame_mdbar_mul
import Theorems.Thm_GlobalTheory_HermFrame_mdbar_inv
import Theorems.Thm_GlobalTheory_HermFrame_mdbar_mdel
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
theorem _root_.solution (h : MContDiffAt 2 H z) (hu : IsUnit (H z).det) (ξ η : E) :
    curv H z ξ η = (H z)ᵀ⁻¹ * (mdbar H z η)ᵀ * (H z)ᵀ⁻¹ * (mdel H z ξ)ᵀ
      - (H z)ᵀ⁻¹ * (mddbar H z ξ η)ᵀ := by
  have h1 : MContDiffAt 1 H z := h.of_le one_le_two
  have hu' : IsUnit (H z)ᵀ.det := by rwa [det_transpose]
  simp only [curv, conn]
  rw [mdbar_mul (h1.transpose.inv hu') (h.mdel (by norm_num) ξ).transpose,
    mdbar_inv h1.transpose hu', mdbar_transpose (fun x => mdel H x ξ), mdbar_mdel h,
    mdbar_transpose, Matrix.neg_mul]
  abel
end GlobalTheory.HermFrame
