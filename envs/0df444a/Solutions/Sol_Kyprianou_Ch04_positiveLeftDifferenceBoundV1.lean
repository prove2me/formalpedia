-- Prove2me | solution 1 for Kyprianou.Ch04.positiveLeftDifferenceBoundV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T22:55:46.059668+00:00
-- url     : https://prove2.me/submissions/3d9b6f53-44c9-4bbf-a60d-355f590e7d20

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal Classical Topology
set_option autoImplicit false

theorem solution
    (Y Z L R : NNReal → ℝ) (T : NNReal) (d : ℝ)
    (hY : ∀ t, 0 < t → Tendsto Y (nhdsWithin t (Iio t)) (nhds (L t)))
    (hZ : ∀ t, 0 < t → Tendsto Z (nhdsWithin t (Iio t)) (nhds (R t)))
    (hb : ∀ t ≤ T, |Y t - Z t| ≤ d) :
    ∀ t ≤ T, 0 < t → |L t - R t| ≤ d := by
  intro t ht ht0
  letI : (nhdsWithin t (Iio t)).NeBot := nhdsLT_neBot_of_exists_lt ⟨0,ht0⟩
  exact le_of_tendsto ((hY t ht0).sub (hZ t ht0)).abs
    ((eventually_mem_nhdsWithin : ∀ᶠ u in nhdsWithin t (Iio t), u ∈ Iio t).mono
      fun u hu => hb u ((le_of_lt hu).trans ht))
