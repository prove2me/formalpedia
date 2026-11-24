-- Prove2me | solution 1 for GlobalTheory.HermFrame.TwoFormBound.mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:40:32.130804+00:00
-- url     : https://prove2.me/submissions/6b428bf5-c17c-42e0-b722-a34a3b712fe2

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
variable [Fintype n]
variable {U : Set (ι → ℂ)} {H : (ι → ℂ) → Matrix n n ℂ} {G : (ι → ℂ) → Matrix ι ι ℂ} {C C' : ℝ}
namespace GlobalTheory.HermFrame
namespace TwoFormBound
theorem _root_.solution {F : (ι → ℂ) → (ι → ℂ) → (ι → ℂ) → Matrix n n ℂ}
    (h : TwoFormBound U H G F C) (hC : C ≤ C') : TwoFormBound U H G F C' := fun z hz =>
  ⟨(h z hz).1, (h z hz).2.1, fun ξ η => ((h z hz).2.2 ξ η).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC (gnorm_nonneg _ _))
      (gnorm_nonneg _ _))⟩
end TwoFormBound
end GlobalTheory.HermFrame
