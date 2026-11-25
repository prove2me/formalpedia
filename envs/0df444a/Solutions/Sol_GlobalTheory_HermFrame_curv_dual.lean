-- Prove2me | solution 1 for GlobalTheory.HermFrame.curv_dual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:46:24.745804+00:00
-- url     : https://prove2.me/submissions/502cc8b3-48e6-45c2-b463-7ea482efc40c

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LeTwoMulOfForallScale
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
import Theorems.Thm_GlobalTheory_HermFrame_mdbar_transpose
import Theorems.Thm_GlobalTheory_HermFrame_mdbar_neg
import Theorems.Thm_GlobalTheory_HermFrame_conn_dual

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
theorem _root_.solution (h : MContDiffAt 2 H z) (hu : IsUnit (H z).det) (ξ η : E) :
    curv (fun x => dualGram (H x)) z ξ η = -(curv H z ξ η)ᵀ := by
  have he : (fun x => conn (fun x => dualGram (H x)) x ξ) =ᶠ[𝓝 z] fun x => -(conn H x ξ)ᵀ := by
    filter_upwards [h.eventually_two, h.eventually_isUnit hu] with x h3 h4
    exact conn_dual (h3.of_le one_le_two) h4 ξ
  rw [curv, mdbar_congr he, mdbar_neg, curv, mdbar_transpose (fun x => conn H x ξ), transpose_neg]
end GlobalTheory.HermFrame
