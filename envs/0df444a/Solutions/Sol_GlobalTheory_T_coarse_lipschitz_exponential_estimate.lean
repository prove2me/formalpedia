-- Prove2me | solution 1 for GlobalTheory.T.coarse_lipschitz_exponential_estimate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:30:08.74113+00:00
-- url     : https://prove2.me/submissions/3074ee47-025a-414a-bb22-05305fa04604

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CoarseLipschitzExponentialEstimate
import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CoarseLipschitzExponentialEstimateStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_EisCross_dom


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] (Γ Δ P P' : Subgroup G) (ξ l₁ l₂ : G → ℝ) (H : ℂ → G → X)
    (a b e₁ e₂ M : ℝ),
    (∀ C : Set G, IsCompact C → ∃ A : ℝ, ∀ g, ∀ u ∈ C, |ξ (g * u) - ξ g| ≤ A) →
    (∀ C : Set G, IsCompact C → ∃ A : ℝ, ∀ g, ∀ u ∈ C, |l₁ (g * u) - l₁ g| ≤ A) →
    (∀ C : Set G, IsCompact C → ∃ A : ℝ, ∀ g, ∀ u ∈ C, |l₂ (g * u) - l₂ g| ≤ A) →
    PositivityTheory.RgEis.Conv Δ P l₁ → PositivityTheory.RgEis.Conv Δ P' l₂ →
    (∀ z : ℂ, b ≤ z.re → z.re ≤ a → ∀ g, ‖H z g‖ ≤ M * (PositivityTheory.RgEis.pos Δ P l₁ g + PositivityTheory.RgEis.pos Δ P' l₂ g)) →
    (∀ g, Summable fun r : PositivityTheory.RgEis.Cos Δ Γ => Real.exp (e₁ * ξ (PositivityTheory.RgEis.rep r * g)) *
      PositivityTheory.RgEis.pos Δ P l₁ (PositivityTheory.RgEis.rep r * g)) →
    (∀ g, Summable fun r : PositivityTheory.RgEis.Cos Δ Γ => Real.exp (e₂ * ξ (PositivityTheory.RgEis.rep r * g)) *
      PositivityTheory.RgEis.pos Δ P l₁ (PositivityTheory.RgEis.rep r * g)) →
    (∀ g, Summable fun r : PositivityTheory.RgEis.Cos Δ Γ => Real.exp (e₁ * ξ (PositivityTheory.RgEis.rep r * g)) *
      PositivityTheory.RgEis.pos Δ P' l₂ (PositivityTheory.RgEis.rep r * g)) →
    (∀ g, Summable fun r : PositivityTheory.RgEis.Cos Δ Γ => Real.exp (e₂ * ξ (PositivityTheory.RgEis.rep r * g)) *
      PositivityTheory.RgEis.pos Δ P' l₂ (PositivityTheory.RgEis.rep r * g)) →
    ∀ g : G, ∃ U ∈ 𝓝 g, ∃ u : PositivityTheory.RgEis.Cos Δ Γ → ℝ, Summable u ∧
      ∀ l : ℂ × ℂ, b ≤ l.1.re → l.1.re ≤ a → e₁ ≤ l.2.re → l.2.re ≤ e₂ → ∀ g' ∈ U, ∀ r,
        ‖Complex.exp (l.2 * ξ (PositivityTheory.RgEis.rep r * g')) • H l.1 (PositivityTheory.RgEis.rep r * g')‖ ≤ u r := by
  first | exact @GlobalTheory.CompanionTheory.EisCross.dom | exact GlobalTheory.CompanionTheory.EisCross.dom | (intros; apply GlobalTheory.CompanionTheory.EisCross.dom <;> assumption)
end _root_.GlobalTheory.T
