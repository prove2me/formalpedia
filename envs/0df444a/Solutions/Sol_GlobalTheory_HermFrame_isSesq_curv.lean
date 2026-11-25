-- Prove2me | solution 1 for GlobalTheory.HermFrame.isSesq_curv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:01:23.189432+00:00
-- url     : https://prove2.me/submissions/ea0a4910-6dae-4df4-885c-5117e2e22ba2

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LeTwoMulOfForallScale
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
import Theorems.Thm_GlobalTheory_HermFrame_mdel_add_vec
import Theorems.Thm_GlobalTheory_HermFrame_mdel_smul_vec
import Theorems.Thm_GlobalTheory_HermFrame_mdbar_add_vec
import Theorems.Thm_GlobalTheory_HermFrame_mdbar_smul_vec
import Theorems.Thm_GlobalTheory_HermFrame_isSesq_mddbar
import Theorems.Thm_GlobalTheory_HermFrame_curv_eq
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
theorem _root_.solution (h : MContDiffAt 2 H z) (hu : IsUnit (H z).det) : IsSesq (curv H z) := by
  have hs := isSesq_mddbar H z
  constructor <;> intros <;>
    simp only [curv_eq h hu, mdel_add_vec, mdbar_add_vec, mdel_smul_vec, mdbar_smul_vec,
      hs.add_left, hs.add_right, hs.smul_left, hs.smul_right, transpose_add, transpose_smul,
      Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, smul_sub] <;> abel
end GlobalTheory.HermFrame
