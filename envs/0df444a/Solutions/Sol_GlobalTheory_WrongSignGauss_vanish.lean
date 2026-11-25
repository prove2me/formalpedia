-- Prove2me | solution 1 for GlobalTheory.WrongSignGauss.vanish
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:48:32.015573+00:00
-- url     : https://prove2.me/submissions/e7420533-2153-4800-9670-57108a0773fe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SchwartzEqZeroOfWrongSignGaussianRelation
import Theorems.Thm_GlobalTheory_WrongSignGauss_sesq_apply
import Theorems.Thm_GlobalTheory_WrongSignGauss_twD_apply
import Theorems.Thm_GlobalTheory_WrongSignGauss_integrable_ip
import Theorems.Thm_GlobalTheory_WrongSignGauss_norm_sq_twD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.WrongSignGauss.sesq_apply

set_option autoImplicit false
open SchwartzMap LineDeriv MeasureTheory ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.WrongSignGauss
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
namespace GlobalTheory.WrongSignGauss
theorem _root_.solution : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (f : SchwartzMap V ℂ) (a₁ a₂ : V) (ℓ₁ ℓ₂ : V →ₗ[ℝ] ℝ),
    (∀ y, fderiv ℝ f y a₂ + (-(2 * Real.pi * Complex.I) * (ℓ₂ y : ℂ)) * f y =
      Complex.I * (fderiv ℝ f y a₁ + (-(2 * Real.pi * Complex.I) * (ℓ₁ y : ℂ)) * f y)) →
    ℓ₂ a₁ - ℓ₁ a₂ < 0 → f = 0 := by
  intro V _ _ _ f a₁ a₂ ℓ₁ ℓ₂ hf hc
  letI : MeasurableSpace V := borel V
  haveI : BorelSpace V := ⟨rfl⟩
  let μ : Measure V := Measure.addHaar
  have hD : twD a₂ ℓ₂ f = Complex.I • twD a₁ ℓ₁ f := by
    ext y
    simp only [SchwartzMap.smul_apply, smul_eq_mul, twD_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv]
    linear_combination hf y
  have hk := norm_sq_twD μ f a₁ a₂ ℓ₁ ℓ₂ hD
  have hG : 0 ≤ ∫ x, ‖twD a₁ ℓ₁ f x‖ ^ 2 ∂μ := integral_nonneg (fun x => by positivity)
  have hF : 0 ≤ ∫ x, ‖f x‖ ^ 2 ∂μ := integral_nonneg (fun x => by positivity)
  have hP : Real.pi * (ℓ₂ a₁ - ℓ₁ a₂) < 0 := mul_neg_of_pos_of_neg Real.pi_pos hc
  have hF0 : ∫ x, ‖f x‖ ^ 2 ∂μ = 0 := by nlinarith
  have hint : Integrable (fun x => ‖f x‖ ^ 2) μ := by
    refine (integrable_ip μ f f).norm.congr (Filter.Eventually.of_forall fun x => ?_)
    simp [norm_mul, sq]
  rw [integral_eq_zero_iff_of_nonneg (fun x => by positivity) hint] at hF0
  have hcont : Continuous (fun x => ‖f x‖ ^ 2) := f.continuous.norm.pow 2
  have h0 := (Continuous.ae_eq_iff_eq μ hcont continuous_zero).1 hF0
  ext x
  have hx := congrFun h0 x
  simpa using hx
end GlobalTheory.WrongSignGauss
