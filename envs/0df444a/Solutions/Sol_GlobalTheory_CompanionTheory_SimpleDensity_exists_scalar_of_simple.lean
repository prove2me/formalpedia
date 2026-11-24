-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SimpleDensity.exists_scalar_of_simple
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:38:49.264573+00:00
-- url     : https://prove2.me/submissions/150a6681-7323-49dd-a6b1-5532be3e1f55

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsSmulEqOnFinset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SimpleDensity
namespace GlobalTheory.CompanionTheory.SimpleDensity
theorem _root_.solution {A N : Type} [Ring A] [Algebra ℂ A] [AddCommGroup N] [Module ℂ N] [Module A N]
    [IsScalarTower ℂ A N] [FiniteDimensional ℂ N] [IsSimpleModule A N] (φ : N →ₗ[A] N) :
    ∃ c : ℂ, ∀ x, φ x = c • x := by
  haveI : Nontrivial N := IsSimpleModule.nontrivial A N
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (φ.restrictScalars ℂ : Module.End ℂ N)
  obtain ⟨w, hw⟩ := hc.exists_hasEigenvector
  refine ⟨c, ?_⟩
  have hw1 : φ w = c • w := hw.apply_eq_smul
  let ψ : N →ₗ[A] N := φ - c • LinearMap.id
  rcases LinearMap.injective_or_eq_zero ψ with hi | h0
  · exfalso
    have hz : ψ w = 0 := by simp [ψ, hw1]
    exact hw.2 (hi (by rw [hz, map_zero]))
  · intro x
    have := LinearMap.congr_fun h0 x
    simpa [ψ, sub_eq_zero] using this
end GlobalTheory.CompanionTheory.SimpleDensity
