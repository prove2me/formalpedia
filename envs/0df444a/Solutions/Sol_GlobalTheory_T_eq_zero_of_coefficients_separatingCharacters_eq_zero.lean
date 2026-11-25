-- Prove2me | solution 1 for GlobalTheory.T.eq_zero_of_coefficients_separatingCharacters_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:19:06.208734+00:00
-- url     : https://prove2.me/submissions/27621fe9-0a71-424d-95e6-f58c6d159393

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_EqZeroOfCoefficientsSeparatingCharactersEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_EqZeroOfCoefficientsSeparatingCharactersEqZeroStatement
import Theorems.Thm_GlobalTheory_SeparatingCharacters_eq_zero_of_coefficients_eq_zero


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
theorem _root_.solution : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G) [DiscreteTopology Γ] (K : Set G), IsCompact K → (∀ x, ∃ γ ∈ Γ, γ + x ∈ K) → ∀ (A : Type) [AddCommGroup A] (χ : A → G → ℂ), (∀ a, Continuous (χ a)) → (∀ a x y, χ a (x + y) = χ a x * χ a y) → (∀ a b x, χ (a + b) x = χ a x * χ b x) → (∀ x, χ 0 x = 1) → (∀ a x, ‖χ a x‖ = 1) → (∀ x, (∀ a, χ a x = 1) ↔ x ∈ Γ) → ∀ (μ : Measure G) (𝓕 : Set G), μ.IsAddHaarMeasure → IsAddFundamentalDomain Γ 𝓕 μ → ∀ Φ : G → ℂ, Continuous Φ → (∀ γ ∈ Γ, ∀ x, Φ (γ + x) = Φ x) → (∀ a, ∫ x in 𝓕, χ a x * Φ x ∂μ = 0) → Φ = 0 := by
  first | exact @GlobalTheory.SeparatingCharacters.eq_zero_of_coefficients_eq_zero | exact GlobalTheory.SeparatingCharacters.eq_zero_of_coefficients_eq_zero | (intros; apply GlobalTheory.SeparatingCharacters.eq_zero_of_coefficients_eq_zero <;> assumption)
end _root_.GlobalTheory.T
