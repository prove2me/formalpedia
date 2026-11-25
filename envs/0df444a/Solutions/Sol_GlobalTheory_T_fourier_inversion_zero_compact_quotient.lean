-- Prove2me | solution 1 for GlobalTheory.T.fourier_inversion_zero_compact_quotient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:19:36.526576+00:00
-- url     : https://prove2.me/submissions/0f7b5b16-50d8-45ed-a303-3ccb965c3dad

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierInversionZeroCompactQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierInversionZeroCompactQuotientStatement
import Theorems.Thm_GlobalTheory_CompactQuotientFourier_inversion_at_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G) [DiscreteTopology Γ] (K : Set G), IsCompact K → (∀ x, ∃ γ ∈ Γ, γ + x ∈ K) → ∀ (A : Type) [AddCommGroup A] [Countable A] (χ : A → G → ℂ), (∀ a, Continuous (χ a)) → (∀ a x y, χ a (x + y) = χ a x * χ a y) → (∀ a b x, χ (a + b) x = χ a x * χ b x) → (∀ a x, ‖χ a x‖ = 1) → (∀ x, (∀ a, χ a x = 1) ↔ x ∈ Γ) → (∀ a, (∀ x, χ a x = 1) → a = 0) → ∀ (μ : Measure G) (𝓕 : Set G), μ.IsAddHaarMeasure → IsAddFundamentalDomain Γ 𝓕 μ → μ 𝓕 = 1 → ∀ Φ : G → ℂ, Continuous Φ → (∀ γ ∈ Γ, ∀ x, Φ (γ + x) = Φ x) → Summable (fun a => ‖∫ x in 𝓕, χ a x * Φ x ∂μ‖) → Φ 0 = ∑' a, ∫ x in 𝓕, χ a x * Φ x ∂μ := by
  first | exact @GlobalTheory.CompactQuotientFourier.inversion_at_zero | exact GlobalTheory.CompactQuotientFourier.inversion_at_zero | (intros; apply GlobalTheory.CompactQuotientFourier.inversion_at_zero <;> assumption)
end _root_.GlobalTheory.T
