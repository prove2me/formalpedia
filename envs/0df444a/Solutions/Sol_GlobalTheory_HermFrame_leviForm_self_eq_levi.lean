-- Prove2me | solution 1 for GlobalTheory.HermFrame.leviForm_self_eq_levi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:40:31.460112+00:00
-- url     : https://prove2.me/submissions/a7c585de-60ec-4427-8ca4-5ad805a9473b

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LeTwoMulOfForallScale
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
import Theorems.Thm_GlobalTheory_leviForm_apply_self


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
variable {ι : Type*} [Fintype ι]
namespace GlobalTheory.HermFrame
theorem _root_.solution {u : (ι → ℂ) → ℝ} {z : ι → ℂ} (hu : ContDiffAt ℝ 2 u z)
    (ξ : ι → ℂ) : leviForm u z ξ ξ = ReciprocityTheory.AnForm.levi u z ξ := by
  rw [leviForm_apply_self hu, ReciprocityTheory.AnForm.levi]; congr 1; ring
end GlobalTheory.HermFrame
