-- Prove2me | solution 1 for GlobalTheory.HermFrame.diagVal_formOf_eq_gnorm_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:49:41.659952+00:00
-- url     : https://prove2.me/submissions/ad6be757-146d-4005-9288-25fe815439c6

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LeTwoMulOfForallScale
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
import Theorems.Thm_GlobalTheory_HermFrame_diagVal_formOf
import Theorems.Thm_GlobalTheory_HermFrame_gnorm_sq


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
theorem _root_.solution {G : Matrix ι ι ℂ} (hG : G.PosSemidef) (ξ : ι → ℂ) :
    diagVal (formOf G) ξ = gnorm G ξ ^ 2 := by rw [diagVal_formOf, gnorm_sq hG]
end GlobalTheory.HermFrame
