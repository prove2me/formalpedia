-- Prove2me | solution 1 for GlobalTheory.HermFrame.diagVal_ddc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:51:20.101476+00:00
-- url     : https://prove2.me/submissions/83e6eff0-cc39-427f-9186-3dca84e785da

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LeTwoMulOfForallScale
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
import Theorems.Thm_GlobalTheory_HermFrame_leviForm_self_eq_levi

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
theorem _root_.solution {u : (ι → ℂ) → ℝ} {z : ι → ℂ} (hu : ContDiffAt ℝ 2 u z) (ξ : ι → ℂ) :
    diagVal (ddc u z) ξ = ReciprocityTheory.AnForm.levi u z ξ / (2 * Real.pi) := by
  have : -I * (kappa * (ReciprocityTheory.AnForm.levi u z ξ : ℂ)) =
      ((ReciprocityTheory.AnForm.levi u z ξ / (2 * Real.pi) : ℝ) : ℂ) := by
    rw [kappa]; push_cast; linear_combination (-(ReciprocityTheory.AnForm.levi u z ξ : ℂ) /
      (2 * Real.pi)) * I_mul_I
  rw [diagVal, ddc, leviForm_self_eq_levi hu, this, ofReal_re]
end GlobalTheory.HermFrame
