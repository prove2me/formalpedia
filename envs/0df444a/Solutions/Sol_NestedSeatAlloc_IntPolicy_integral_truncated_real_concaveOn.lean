-- Prove2me | solution 1 for NestedSeatAlloc.IntPolicy.integral_truncated_real_concaveOn
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-19T09:06:18.754973+00:00
-- url     : https://prove2.me/submissions/9f76a370-ff50-47ae-a6ac-df3dfeb2e503

import Mathlib
set_option autoImplicit false

open MeasureTheory

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (a : ℝ) (N : Ω → ℝ)
    (hconc : ∀ᵐ ω ∂P,
      ConcaveOn ℝ (Set.Ici 0) (fun s : ℝ => a * min s (N ω)))
    (hint : ∀ s ∈ Set.Ici (0 : ℝ),
      Integrable (fun ω => a * min s (N ω)) P) :
    ConcaveOn ℝ (Set.Ici 0)
      (fun s : ℝ => ∫ ω, a * min s (N ω) ∂P) := by
  refine ⟨convex_Ici 0, ?_⟩
  intro x hx y hy p q hp hq hpq
  have hz : p • x + q • y ∈ Set.Ici (0:ℝ) := (convex_Ici (0:ℝ)) hx hy hp hq hpq
  have h1 : Integrable (fun ω => p • (a * min x (N ω)) + q • (a * min y (N ω))) P :=
    ((hint x hx).smul p).add ((hint y hy).smul q)
  have h2 := hint _ hz
  have hle : (fun ω => p • (a * min x (N ω)) + q • (a * min y (N ω))) ≤ᵐ[P]
      (fun ω => a * min (p • x + q • y) (N ω)) := by
    filter_upwards [hconc] with ω hω
    exact hω.2 hx hy hp hq hpq
  have := integral_mono_ae h1 h2 hle
  have e : ∫ ω, (p • (a * min x (N ω)) + q • (a * min y (N ω))) ∂P
      = p • ∫ ω, a * min x (N ω) ∂P + q • ∫ ω, a * min y (N ω) ∂P := by
    have i1 : Integrable (fun ω => p • (a * min x (N ω))) P := (hint x hx).smul p
    have i2 : Integrable (fun ω => q • (a * min y (N ω))) P := (hint y hy).smul q
    rw [integral_add i1 i2, integral_smul, integral_smul]
  exact e.symm.le.trans this
