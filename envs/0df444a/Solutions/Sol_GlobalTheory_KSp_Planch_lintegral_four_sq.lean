-- Prove2me | solution 1 for GlobalTheory.KSp.Planch.lintegral_four_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:27:00.779614+00:00
-- url     : https://prove2.me/submissions/82c4ba91-60cc-4b84-b7d0-a79097259bf2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BicharacterFourierTransformMemSchwartzBruhatStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LintegralFourSq
import Theorems.Thm_GlobalTheory_KSp_Planch_integral_four_mul
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_continuous
import Theorems.Thm_GlobalTheory_T_bicharacterFourierTransform_mem_schwartzBruhat


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
noncomputable section
open GlobalTheory GlobalTheory.KSp GlobalTheory.KSp.Planch
variable {X : Type} [AddCommGroup X] [TopologicalSpace X]
namespace GlobalTheory.KSp.Planch
theorem _root_.solution : ∀ (X : Type) [AddCommGroup X] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] (_ : Good X) (μ : Measure X) [μ.IsAddHaarMeasure] (e : X → X → ℂ), IsPair e → ∀ C : ℝ, 0 < C → (∀ φ ∈ SB X, ∀ x, four μ e (four μ e φ) x = (C : ℂ) * φ (-x)) → ∀ φ ∈ SB X, ∫⁻ x, ‖four μ e φ x‖ₑ ^ 2 ∂μ = ENNReal.ofReal C * ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ := by
  intro X _ _ _ _ hG μ _ e he C hC hinv φ hφ
  haveI := hG.grp; haveI := hG.t2; haveI := hG.lc; haveI := hG.sc
  have hΦ : four μ e φ ∈ SB X := GlobalTheory.T.bicharacterFourierTransform_mem_schwartzBruhat X hG μ e he φ hφ
  have hL : ∀ f ∈ SB X, ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ = ENNReal.ofReal (∫ x, ‖f x‖ ^ 2 ∂μ) := by
    intro f hf
    have h1 : Continuous f := hf.1.continuous
    have h2 : HasCompactSupport f := hf.2
    have h3 : HasCompactSupport (fun x => ‖f x‖ ^ 2) := by
      have := h2.norm
      exact this.mul_right (f' := fun x => ‖f x‖) |>.mono (fun x hx => by simpa [sq] using hx)
    have hi : Integrable (fun x => ‖f x‖ ^ 2) μ :=
      (h1.norm.pow 2).integrable_of_hasCompactSupport h3
    rw [ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun x => by positivity)]
    congr 1; ext x
    rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_pow (norm_nonneg _)]
  have hC' : ∀ f : X → ℂ, ∫ x, f x * starRingEnd ℂ (f x) ∂μ = ((∫ x, ‖f x‖ ^ 2 ∂μ : ℝ) : ℂ) := by
    intro f
    rw [← integral_complex_ofReal]
    congr 1; ext x
    rw [Complex.mul_conj']
    push_cast; rfl
  have hk := integral_four_mul X hG μ e he C hC hinv φ hφ
  rw [hC', hC'] at hk
  have hk' : ∫ x, ‖four μ e φ x‖ ^ 2 ∂μ = C * ∫ x, ‖φ x‖ ^ 2 ∂μ := by exact_mod_cast hk
  rw [hL _ hΦ, hL _ hφ, hk', ENNReal.ofReal_mul hC.le]
end GlobalTheory.KSp.Planch
