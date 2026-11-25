-- Prove2me | solution 1 for GlobalTheory.WrongSignGauss.norm_sq_twD
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:12:44.941849+00:00
-- url     : https://prove2.me/submissions/62dea7f9-8f65-431b-8e67-d54db47590ed

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SchwartzEqZeroOfWrongSignGaussianRelation
import Theorems.Thm_GlobalTheory_WrongSignGauss_sesq_apply
import Theorems.Thm_GlobalTheory_WrongSignGauss_ip_smul_left
import Theorems.Thm_GlobalTheory_WrongSignGauss_ip_smul_right
import Theorems.Thm_GlobalTheory_WrongSignGauss_ip_sub_left
import Theorems.Thm_GlobalTheory_WrongSignGauss_ip_twD
import Theorems.Thm_GlobalTheory_WrongSignGauss_twD_comm
import Theorems.Thm_GlobalTheory_WrongSignGauss_ip_self
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
variable [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure]
namespace GlobalTheory.WrongSignGauss
theorem _root_.solution (f : 𝓢(V, ℂ)) (a₁ a₂ : V) (ℓ₁ ℓ₂ : V →ₗ[ℝ] ℝ)
    (hD : twD a₂ ℓ₂ f = Complex.I • twD a₁ ℓ₁ f) :
    ∫ x, ‖twD a₁ ℓ₁ f x‖ ^ 2 ∂μ = Real.pi * (ℓ₂ a₁ - ℓ₁ a₂) * ∫ x, ‖f x‖ ^ 2 ∂μ := by
  have h1 : ip μ (twD a₁ ℓ₁ (twD a₂ ℓ₂ f)) f = -(Complex.I * ip μ (twD a₁ ℓ₁ f) (twD a₁ ℓ₁ f)) := by
    rw [ip_twD, hD, ip_smul_left]
  have h2 : ip μ (twD a₂ ℓ₂ (twD a₁ ℓ₁ f)) f = -(conj Complex.I * ip μ (twD a₁ ℓ₁ f) (twD a₁ ℓ₁ f)) := by
    rw [ip_twD, hD, ip_smul_right]
  have h3 := congrArg (fun u => ip μ u f) (twD_comm a₁ a₂ ℓ₁ ℓ₂ f)
  simp only [ip_sub_left, ip_smul_left, h1, h2, Complex.conj_I, ip_self] at h3
  have E : ((∫ x, ‖twD a₁ ℓ₁ f x‖ ^ 2 ∂μ : ℝ) : ℂ) =
      ((Real.pi * (ℓ₂ a₁ - ℓ₁ a₂) * ∫ x, ‖f x‖ ^ 2 ∂μ : ℝ) : ℂ) := by
    push_cast at h3 ⊢
    linear_combination (Complex.I / 2) * h3 +
      (((∫ x, ‖twD a₁ ℓ₁ f x‖ ^ 2 ∂μ : ℝ) : ℂ) - Real.pi * ((ℓ₂ a₁ : ℂ) - ℓ₁ a₂) *
        ((∫ x, ‖f x‖ ^ 2 ∂μ : ℝ) : ℂ)) * Complex.I_sq
  exact_mod_cast E
end GlobalTheory.WrongSignGauss
