-- Prove2me | solution 1 for LeiBR.Sync.fixed_point
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T10:41:57.090278+00:00
-- url     : https://prove2.me/submissions/33ada17d-020c-4225-b287-abd53a8d86c9

import Mathlib
import Definitions.Def_LeiBR_Sync_NashGame
import Definitions.Def_LeiBR_Sync_StochGame

open LeiBR.Sync

open MeasureTheory



theorem solution
    {N : ℕ} {n : Fin N → ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {d : ℕ} (ξ : Ω → EuclideanSpace ℝ (Fin d))
    (X : ∀ i : Fin N, Set (Strat n i)) (ψ : Fin N → Profile n → EuclideanSpace ℝ (Fin d) → ℝ)
    (gψ : ∀ i : Fin N, Profile n → EuclideanSpace ℝ (Fin d) → Strat n i) (M : Fin N → ℝ)
    (hA1 : Assumption1 P ξ X ψ gψ M) (μ : ℝ) (hμ : 0 < μ)
    (xhat : Profile n → Profile n) (hxhat : IsProxBR X (payoff P ξ ψ) μ xhat)
    (xs : Profile n) (hxs : IsNashEq X (payoff P ξ ψ) xs) :
    ∀ i : Fin N, xhat xs i = xs i := by
  intro i
  obtain ⟨hmem, hmin⟩ := hxhat xs hxs.1 i
  have h1 := isMinOn_iff.mp hmin (xs i) (hxs.1 i (Set.mem_univ i))
  simp only [Function.update_eq_self, sub_self, norm_zero] at h1
  have h2 := hxs.2 i (xhat xs i) hmem
  have h3 : ‖xhat xs i - xs i‖ ^ 2 ≤ 0 := by
    have : μ / 2 * ‖xhat xs i - xs i‖ ^ 2 ≤ 0 := by nlinarith
    by_contra hc
    push_neg at hc
    have : 0 < μ / 2 * ‖xhat xs i - xs i‖ ^ 2 := by positivity
    linarith
  have h4 : ‖xhat xs i - xs i‖ = 0 := by nlinarith [norm_nonneg (xhat xs i - xs i)]
  exact sub_eq_zero.mp (norm_eq_zero.mp h4)
