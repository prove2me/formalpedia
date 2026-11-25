-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Entire.local_factorisation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:37:48.702925+00:00
-- url     : https://prove2.me/submissions/c5509c29-5c68-4bfd-b36e-c2486c4c81f5

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LocalFactorisationHolomorphic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Entire
namespace GlobalTheory.CompanionTheory.Entire
theorem _root_.solution :
    ∀ A : ℂ → ℂ, Differentiable ℂ A → (∃ z, A z ≠ 0) → ∀ s₀ : ℂ,
      ∃ (k : ℕ) (U : Set ℂ) (u : ℂ → ℂ), IsOpen U ∧ s₀ ∈ U ∧ DifferentiableOn ℂ u U ∧
        ∀ s ∈ U, u s ≠ 0 ∧ A s = (s - s₀) ^ k * u s := by
  intro A hA hne s₀
  have han : AnalyticAt ℂ A s₀ := hA.analyticAt s₀
  have hnz : ¬ ∀ᶠ z in 𝓝 s₀, A z = 0 := by
    intro hev
    obtain ⟨z, hz⟩ := hne
    exact hz (AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (fun w _ => hA.analyticAt w) isPreconnected_univ (Set.mem_univ s₀) hev (Set.mem_univ z))
  obtain ⟨n, g, hg, hg0, hev⟩ := han.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hnz
  have hall : ∀ᶠ z in 𝓝 s₀, AnalyticAt ℂ g z ∧ g z ≠ 0 ∧ A z = (z - s₀) ^ n * g z :=
    hg.eventually_analyticAt.and ((hg.continuousAt.eventually_ne hg0).and
      (hev.mono fun z hz => by simpa [smul_eq_mul] using hz))
  obtain ⟨U, hU, hUo, hsU⟩ := eventually_nhds_iff.mp hall
  exact ⟨n, U, g, hUo, hsU, fun z hz => (hU z hz).1.differentiableAt.differentiableWithinAt,
    fun z hz => ⟨(hU z hz).2.1, (hU z hz).2.2⟩⟩
end GlobalTheory.CompanionTheory.Entire
