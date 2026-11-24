-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisGal.chain4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:05:21.126572+00:00
-- url     : https://prove2.me/submissions/1abd2687-72df-4570-b914-882c2405ccd8

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DifferentiableAffLine
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ChamberPairThreeFour

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology PositivityTheory.RgEis
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEisGal
namespace GlobalTheory.CompanionTheory.RgEisGal
theorem _root_.solution (hTC : TubeChain) {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    {T : Type} [TopologicalSpace T] [FirstCountableTopology T] {Ω₀ Ω₁ Ω₂ Ω₃ : Set (ℝ × ℝ)}
    {F₀ F₁ F₂ F₃ : ℂ × ℂ → T → X}
    (h₀ : IsOpen Ω₀ ∧ Convex ℝ Ω₀ ∧ TubeGood F₀ Ω₀) (h₁ : IsOpen Ω₁ ∧ Convex ℝ Ω₁ ∧ TubeGood F₁ Ω₁)
    (h₂ : IsOpen Ω₂ ∧ Convex ℝ Ω₂ ∧ TubeGood F₂ Ω₂) (h₃ : IsOpen Ω₃ ∧ Convex ℝ Ω₃ ∧ TubeGood F₃ Ω₃)
    (j₀ : ∃ V : Set (ℝ × ℝ), IsOpen V ∧ V.Nonempty ∧ V ⊆ Ω₀ ∩ Ω₁ ∧ ∀ l ∈ tube V, ∀ g, F₀ l g = F₁ l g)
    (j₁ : ∃ V : Set (ℝ × ℝ), IsOpen V ∧ V.Nonempty ∧ V ⊆ Ω₁ ∩ Ω₂ ∧ ∀ l ∈ tube V, ∀ g, F₁ l g = F₂ l g)
    (j₂ : ∃ V : Set (ℝ × ℝ), IsOpen V ∧ V.Nonempty ∧ V ⊆ Ω₂ ∩ Ω₃ ∧ ∀ l ∈ tube V, ∀ g, F₂ l g = F₃ l g)
    (mid : ∀ x : ℝ × ℝ, ∃ a ∈ Ω₀, ∃ b ∈ Ω₃, x = midpoint ℝ a b) :
    ∃ Φ : ℂ × ℂ → T → X, TubeGood Φ Set.univ ∧
      (∀ l ∈ tube Ω₀, ∀ g, Φ l g = Complex.exp (l.1 ^ 2 + l.2 ^ 2) • F₀ l g) ∧
      ∀ l ∈ tube Ω₃, ∀ g, Φ l g = Complex.exp (l.1 ^ 2 + l.2 ^ 2) • F₃ l g := by
  obtain ⟨Φ, hΦ, hE⟩ := hTC X T 3 ![Ω₀, Ω₁, Ω₂, Ω₃] ![F₀, F₁, F₂, F₃]
    (by intro i; fin_cases i; exacts [h₀, h₁, h₂, h₃])
    (by intro i; fin_cases i; exacts [j₀, j₁, j₂])
    (by intro x; obtain ⟨a, ha, b, hb, e⟩ := mid x; exact ⟨0, 3, a, ha, b, hb, e⟩)
  exact ⟨Φ, hΦ, hE 0, hE 3⟩
end GlobalTheory.CompanionTheory.RgEisGal
