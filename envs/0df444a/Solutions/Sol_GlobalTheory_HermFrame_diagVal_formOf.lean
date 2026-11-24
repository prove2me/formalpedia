-- Prove2me | solution 1 for GlobalTheory.HermFrame.diagVal_formOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:40:30.715886+00:00
-- url     : https://prove2.me/submissions/fc833fc2-6658-48fd-ae90-f31d58b73ebb

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LeTwoMulOfForallScale
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm

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
theorem _root_.solution (G : Matrix ι ι ℂ) (ξ : ι → ℂ) :
    diagVal (formOf G) ξ = (form G ξ ξ).re := by
  rw [diagVal, formOf, ← mul_assoc, neg_mul, I_mul_I, neg_neg, one_mul]
end GlobalTheory.HermFrame
