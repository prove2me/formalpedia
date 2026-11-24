-- Prove2me | solution 1 for GlobalTheory.RealWeil.Osc.integrable_pow_gau
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:53:02.573962+00:00
-- url     : https://prove2.me/submissions/4058ff17-05b9-42b7-8848-115a7c4750a9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralGauTwistedConv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowMulNormGauLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOscillatorActionOfGaussianPairings
import Theorems.Thm_GlobalTheory_RealWeil_norm_gau


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder
open GlobalTheory GlobalTheory.RealWeil GlobalTheory.RealWeil.Osc
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] {J : V ≃ₗᵢ[ℝ] V}
  {ρ ρ' : V → B →L[ℂ] B}
set_option linter.unusedSectionVars false
namespace GlobalTheory.RealWeil.Osc
theorem _root_.solution (n : ℕ) : Integrable fun w : V => ‖w‖ ^ n * ‖gau w‖ := by
  have h1 := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := V) (b := (π / 4 : ℂ))
    (by simpa using Real.pi_pos) 0 0).norm
  refine Integrable.mono' (h1.const_mul (n.factorial * Real.exp 1))
    ((continuous_norm.pow n).mul continuous_gau.norm).aestronglyMeasurable (Filter.Eventually.of_forall fun w => ?_)
  have e : (-(π / 4 : ℂ) * (‖w‖ : ℂ) ^ 2 + 0 * ((⟪(0 : V), w⟫ : ℝ) : ℂ)) = ((-(π / 4) * ‖w‖ ^ 2 : ℝ) : ℂ) := by
    push_cast; ring
  rw [e, Complex.norm_exp, ofReal_re, Real.norm_of_nonneg (by positivity), norm_gau]
  have h2 : ‖w‖ ^ n ≤ n.factorial * Real.exp ‖w‖ := by
    have := Real.pow_div_factorial_le_exp ‖w‖ (norm_nonneg w) n
    rwa [div_le_iff₀' (by positivity)] at this
  calc ‖w‖ ^ n * Real.exp (-(π / 2) * ‖w‖ ^ 2) ≤ n.factorial * Real.exp ‖w‖ * Real.exp (-(π / 2) * ‖w‖ ^ 2) := by
        gcongr
    _ ≤ _ := by
        rw [mul_assoc, mul_assoc, ← Real.exp_add, ← Real.exp_add]
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
        nlinarith [Real.pi_gt_three, sq_nonneg ‖w‖, sq_nonneg (‖w‖ - 1)]
end GlobalTheory.RealWeil.Osc
