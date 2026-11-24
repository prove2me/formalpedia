-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HolFamily.functional_commutes_iteratedDeriv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:55:13.120867+00:00
-- url     : https://prove2.me/submissions/c9632b18-d0cb-404c-9797-644f6438f77f

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContinuousOnIteratedDerivFamily
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AutomorphicFunctionalHolomorphicDerivative
import Theorems.Thm_GlobalTheory_CompanionTheory_HolFamily_hasDerivAt_functional
import Theorems.Thm_GlobalTheory_CompanionTheory_HolFamily_iteratedDeriv_functional

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Topology Filter
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HolFamily
namespace GlobalTheory.CompanionTheory.HolFamily
theorem _root_.solution :
    ∀ {G : Type} [Group G] [TopologicalSpace G] (Γ : Subgroup G) (Lf : (G → ℂ) → ℂ), (∀ (a : ℂ) (f f' : G → ℂ), Continuous f → Continuous f' → (∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) → (∀ γ ∈ Γ, ∀ g, f' (γ * g) = f' g) → Lf (a • f + f') = a * Lf f + Lf f') → (∃ C : Set G, IsCompact C ∧ ∀ (f : G → ℂ) (M : ℝ), Continuous f → (∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) → (∀ x ∈ C, ‖f x‖ ≤ M) → ‖Lf f‖ ≤ M) → ∀ (U : Set ℂ) (Ê : ℂ → G → ℂ), IsOpen U → (∀ g, DifferentiableOn ℂ (Ê · g) U) → ContinuousOn (fun y : ℂ × G => Ê y.1 y.2) (U ×ˢ Set.univ) → (∀ z ∈ U, ∀ γ ∈ Γ, ∀ g, Ê z (γ * g) = Ê z g) → DifferentiableOn ℂ (fun z => Lf (Ê z)) U ∧ ∀ z ∈ U, ∀ j : ℕ, iteratedDeriv j (fun z => Lf (Ê z)) z = Lf fun g => iteratedDeriv j (Ê · g) z := by
  intro G _ _ Γ Lf hlin hCex U Ê hU hd hc hinv
  obtain ⟨C, hC, hb⟩ := hCex
  exact ⟨fun z hz => (hasDerivAt_functional Γ Lf hlin hC hb hU hd hc hinv hz).differentiableAt.differentiableWithinAt,
    fun z hz j => iteratedDeriv_functional Γ Lf hlin hC hb hU j Ê hd hc hinv z hz⟩
end GlobalTheory.CompanionTheory.HolFamily
