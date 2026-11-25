-- Prove2me | solution 1 for GlobalTheory.HermFrame.conn_smul_vec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:48:28.137992+00:00
-- url     : https://prove2.me/submissions/9b06790c-8978-4207-9912-227abde29594

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LeTwoMulOfForallScale
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
import Theorems.Thm_GlobalTheory_HermFrame_mdel_smul_vec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
theorem _root_.solution (H : E → Matrix n n ℂ) (z : E) (c : ℂ) (ξ : E) :
    conn H z (c • ξ) = c • conn H z ξ := by
  rw [conn, mdel_smul_vec, transpose_smul, Matrix.mul_smul]; rfl
end GlobalTheory.HermFrame
