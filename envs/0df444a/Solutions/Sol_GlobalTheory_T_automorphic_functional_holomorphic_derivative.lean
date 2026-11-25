-- Prove2me | solution 1 for GlobalTheory.T.automorphic_functional_holomorphic_derivative
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:12:51.542827+00:00
-- url     : https://prove2.me/submissions/d779b87e-94c0-4263-813d-c1000fbfc9e6

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AutomorphicFunctionalHolomorphicDerivative
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AutomorphicFunctionalHolomorphicDerivativeStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_HolFamily_functional_commutes_iteratedDeriv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Topology Filter
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {G : Type} [Group G] [TopologicalSpace G] (Γ : Subgroup G) (Lf : (G → ℂ) → ℂ), (∀ (a : ℂ) (f f' : G → ℂ), Continuous f → Continuous f' → (∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) → (∀ γ ∈ Γ, ∀ g, f' (γ * g) = f' g) → Lf (a • f + f') = a * Lf f + Lf f') → (∃ C : Set G, IsCompact C ∧ ∀ (f : G → ℂ) (M : ℝ), Continuous f → (∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) → (∀ x ∈ C, ‖f x‖ ≤ M) → ‖Lf f‖ ≤ M) → ∀ (U : Set ℂ) (Ê : ℂ → G → ℂ), IsOpen U → (∀ g, DifferentiableOn ℂ (Ê · g) U) → ContinuousOn (fun y : ℂ × G => Ê y.1 y.2) (U ×ˢ Set.univ) → (∀ z ∈ U, ∀ γ ∈ Γ, ∀ g, Ê z (γ * g) = Ê z g) → DifferentiableOn ℂ (fun z => Lf (Ê z)) U ∧ ∀ z ∈ U, ∀ j : ℕ, iteratedDeriv j (fun z => Lf (Ê z)) z = Lf fun g => iteratedDeriv j (Ê · g) z := by
  first | exact @GlobalTheory.CompanionTheory.HolFamily.functional_commutes_iteratedDeriv | exact GlobalTheory.CompanionTheory.HolFamily.functional_commutes_iteratedDeriv | (intros; apply GlobalTheory.CompanionTheory.HolFamily.functional_commutes_iteratedDeriv <;> assumption)
end _root_.GlobalTheory.T
