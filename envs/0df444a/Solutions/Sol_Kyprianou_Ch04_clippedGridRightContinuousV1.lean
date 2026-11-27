-- Prove2me | solution 1 for Kyprianou.Ch04.clippedGridRightContinuousV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:56:15.851167+00:00
-- url     : https://prove2.me/submissions/ee8a8e5c-c2e9-4186-ba27-47fa8456cb00

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_Exercise4_5CertificationV3
open MeasureTheory Filter Set Topology LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

/-- A finite clipped grid sum of a right-continuous path remains right continuous. -/
theorem solution  (Y : NNReal → ℝ)
    (hr : ∀ t, Tendsto Y (𝓝[>] t) (𝓝 (Y t)))
    (u : ℕ → NNReal) (n : ℕ) (H : ℕ → ℝ) :
    let G := fun t : NNReal => ∑ k ∈ Finset.range n,
      H k * (Y (min t (u (k+1)))-Y (min t (u k)))
    ∀ t, Tendsto G (𝓝[>] t) (𝓝 (G t)) := by
  intro G t
  have hm (r : NNReal) : Tendsto (fun s => Y (min s r)) (𝓝[>] t) (𝓝 (Y (min t r))) := by
    by_cases ht : r ≤ t
    · rw [min_eq_right ht]
      apply tendsto_const_nhds.congr'
      filter_upwards [self_mem_nhdsWithin] with s hs
      simp [min_eq_right (ht.trans (le_of_lt hs))]
    · have hlt : t < r := lt_of_not_ge ht
      rw [min_eq_left hlt.le]
      apply (hr t).congr'
      filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hlt)] with s hs
      have hs' : s < r := hs
      simp [min_eq_left hs'.le]
  dsimp [G]
  apply tendsto_finset_sum
  intro k hk
  exact tendsto_const_nhds.mul ((hm (u (k+1))).sub (hm (u k)))
