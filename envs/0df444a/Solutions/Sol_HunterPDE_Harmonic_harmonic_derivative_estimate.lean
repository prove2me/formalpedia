-- Prove2me | solution 1 for HunterPDE.Harmonic.harmonic_derivative_estimate
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-09T15:03:32.942689+00:00
-- url     : https://prove2.me/submissions/dae1dc1a-a640-4ab8-9d70-69a1a836ec1d

import Definitions.Def_HunterPDE_Shared_PartialDeriv
import Theorems.Thm_HunterPDE_Harmonic_mean_value_property
import Theorems.Thm_HunterPDE_Harmonic_directional_derivative_mean_value
import Theorems.Thm_MeasureTheory_abs_average_directional_derivative_ball_le

open MeasureTheory HunterPDE.Harmonic
set_option autoImplicit false

theorem solution {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hΩ : IsOpen Ω)
    (hu : InnerProductSpace.HarmonicOnNhd u Ω)
    {x : EuclideanSpace ℝ (Fin n)} {r : ℝ} (hr : 0 < r)
    (hball : Metric.closedBall x r ⊆ Ω) (i : Fin n) {M : ℝ}
    (hM : ∀ y ∈ Metric.closedBall x r, |u y| ≤ M) :
    |HunterPDE.Shared.partialDeriv u i x| ≤ (n / r) * M := by
  have hn : 0 < n := (Nat.zero_le i.val).trans_lt i.isLt
  have hc : ∀ y ∈ Ω, ContDiffAt ℝ 1 u y :=
    fun y hy => (hu y hy).1.of_le (by norm_num)
  have hmv : HasMeanValueProperty Ω u :=
    fun y s hs hsub => HunterPDE.Harmonic.mean_value_property hn hΩ hu hs hsub
  have hd := HunterPDE.Harmonic.directional_derivative_mean_value hn hΩ hc hmv
    hr hball (EuclideanSpace.single i 1)
  change |fderiv ℝ u x (EuclideanSpace.single i 1)| ≤ _
  rw [hd.1]
  simpa using MeasureTheory.abs_average_directional_derivative_ball_le hn hr
    (fun y hy => hc y (hball hy)) (EuclideanSpace.single i 1) hM
