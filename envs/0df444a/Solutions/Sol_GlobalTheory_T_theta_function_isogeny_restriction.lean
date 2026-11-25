-- Prove2me | solution 1 for GlobalTheory.T.theta_function_isogeny_restriction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:25:49.169939+00:00
-- url     : https://prove2.me/submissions/7f9d7652-b06b-4d16-8a1e-ab57c66d4ee3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ThetaFunctionIsogenyRestriction
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ThetaFunctionIsogenyRestrictionStatement
import Theorems.Thm_GlobalTheory_ThetaTranslJet_exists_translates_jet_ne_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexOrder
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (g : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ), Hm.PosDef → ∀ (Λ : AddSubgroup (Fin g → ℂ)), DiscreteTopology Λ → (∀ v, (∀ a ∈ Λ, ∃ k : ℤ, (star v ⬝ᵥ Hm.mulVec a).im = k) ↔ v ∈ Λ) → ∀ (χ θ : (Fin g → ℂ) → ℂ), Differentiable ℂ θ → θ ≠ 0 → (∀ a ∈ Λ, ‖χ a‖ = 1) → (∀ a ∈ Λ, ∀ z, θ (z + a) = χ a * Complex.exp (Real.pi * (star a ⬝ᵥ Hm.mulVec z) + Real.pi / 2 * (star a ⬝ᵥ Hm.mulVec a)) * θ z) → ∀ (M : ℕ) (Λ₁ : AddSubgroup (Fin g → ℂ)), Λ₁ ≤ Λ → (∀ v, (∀ a ∈ Λ₁, ∃ k : ℤ, (star v ⬝ᵥ Hm.mulVec a).im = M * k) ↔ v ∈ Λ₁) → ∀ (n : ℕ) (P : MvPolynomial (Fin n × Fin g) ℂ), P ≠ 0 → P.totalDegree + 2 ≤ M → ∃ y : Fin n → Fin g → ℂ, (∀ b, (M : ℂ) • y b ∈ Λ₁) ∧ ReciprocityTheory.ChartRestriction.G.I2.polyDeriv P (fun q => (Pi.single q.1 (Pi.single q.2 (1 : ℂ) : Fin g → ℂ) : Fin n → Fin g → ℂ)) (fun z : Fin n → Fin g → ℂ => ∏ b, Complex.exp (-(Real.pi * (star (y b) ⬝ᵥ Hm.mulVec (z b)))) * θ (z b + y b)) 0 ≠ 0 := by
  first | exact @GlobalTheory.ThetaTranslJet.exists_translates_jet_ne_zero | exact GlobalTheory.ThetaTranslJet.exists_translates_jet_ne_zero | (intros; apply GlobalTheory.ThetaTranslJet.exists_translates_jet_ne_zero <;> assumption)
end _root_.GlobalTheory.T
