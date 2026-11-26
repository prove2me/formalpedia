-- Prove2me | solution 1 for Kyprianou.Ch04.exercise45LeftLimitUniformV2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T17:10:07.264751+00:00
-- url     : https://prove2.me/submissions/d68529a3-f398-4395-82b7-88404e87e751

import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_5CertificationV3
open MeasureTheory ProbabilityTheory Filter Set Topology LevyStochCalc.Poisson
open scoped NNReal ENNReal Classical Topology
set_option autoImplicit false
theorem solution
    (U : ℕ → NNReal → ℝ) (L : ℕ → NNReal → ℝ)
    (X Y : NNReal → ℝ)
    (hL : ∀ n t, 0 < t → Tendsto (U n) (nhdsWithin t (Iio t)) (nhds (L n t)))
    (hY : ∀ t, 0 < t → Tendsto X (nhdsWithin t (Iio t)) (nhds (Y t)))
    (hConv : ∀ T : NNReal, ∀ δ : ℝ, 0 < δ →
      ∃ N : ℕ, ∀ n ≥ N, ∀ t ≤ T, |U n t-X t| < δ) :
    ∀ t : NNReal, 0 < t → Tendsto (fun n => L n t) atTop (nhds (Y t)) := by
  intro t ht
  letI : (nhdsWithin t (Iio t)).NeBot := nhdsLT_neBot_of_exists_lt ⟨0,ht⟩
  apply Metric.tendsto_atTop.2
  intro δ hd
  obtain ⟨N,hN⟩ := hConv t (δ/2) (by positivity)
  refine ⟨N,fun n hn => ?_⟩
  have hlim := ((hL n t ht).sub (hY t ht)).abs
  have hbound : |L n t-Y t| ≤ δ/2 := le_of_tendsto hlim
    ((eventually_mem_nhdsWithin : ∀ᶠ u in nhdsWithin t (Iio t), u ∈ Iio t).mono
      fun u hu => (hN n hn u (le_of_lt hu)).le)
  rw [Real.dist_eq]
  linarith
