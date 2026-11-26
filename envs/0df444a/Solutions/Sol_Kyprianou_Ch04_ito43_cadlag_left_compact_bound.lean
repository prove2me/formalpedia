-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_cadlag_left_compact_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T17:27:42.654982+00:00
-- url     : https://prove2.me/submissions/f8a0d14e-8699-4dfd-bed3-3fbccb4e1461

import Mathlib
open Set Filter
open scoped NNReal Topology
set_option autoImplicit false

/-- A compact bound on the path bounds every genuine positive left limit on that horizon. -/
theorem solution (X L : NNReal → ℝ) (T : NNReal) (M : ℝ)
    (hX : ∀ t ≤ T, |X t| ≤ M)
    (hL : ∀ t : NNReal, 0 < t → Tendsto X (nhdsWithin t (Iio t)) (nhds (L t))) :
    ∀ t : NNReal, 0 < t → t ≤ T → |L t| ≤ M := by
  intro t ht hT
  have : (nhdsWithin t (Iio t)).NeBot := nhdsLT_neBot_of_exists_lt ⟨0,ht⟩
  apply le_of_tendsto (hL t ht).abs
  filter_upwards [self_mem_nhdsWithin (a := t) (s := Iio t)] with s hs
  exact hX s ((mem_Iio.mp hs).le.trans hT)
