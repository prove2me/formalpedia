-- Prove2me | solution 1 for Kyprianou.Ch02.uniformLimitStrictJumpCapV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:22:55.893542+00:00
-- url     : https://prove2.me/submissions/951efe66-a6be-4cdf-8047-79c9df5b149a

import Mathlib
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    (F : ℕ → ℝ≥0 → ℝ) (f : ℝ≥0 → ℝ) (T : ℝ≥0)
    (c : ℝ) (hc : c < 1)
    (hu : ∀ δ : ℝ, 0 < δ → ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ∀ t : ℝ≥0, t ≤ T → |F n t - f t| < δ)
    (hb : ∀ (n : ℕ) (t : ℝ≥0), 0 < t → t ≤ T →
      ∃ l : ℝ, Tendsto (F n) (nhdsWithin t (Set.Iio t)) (nhds l) ∧
        |F n t - l| ≤ c)
    (t : ℝ≥0) (ht : 0 < t) (htT : t ≤ T)
    (l : ℝ) (hl : Tendsto f (nhdsWithin t (Set.Iio t)) (nhds l)) :
    |f t - l| < 1  := by
  letI : (nhdsWithin t (Set.Iio t)).NeBot :=
    nhdsWithin_Iio_self_neBot' ⟨0, ht⟩
  let δ : ℝ := (1 - c) / 3
  have hδ : 0 < δ := by dsimp [δ]; linarith
  obtain ⟨n, hn⟩ := hu δ hδ
  obtain ⟨ln, hln, hj⟩ := hb n t ht htT
  have hclose : |ln - l| ≤ δ := by
    apply le_of_tendsto (hln.sub hl).abs
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (hn n le_rfl s ((Set.mem_Iio.mp hs).le.trans htT)).le
  have htclose := hn n le_rfl t htT
  have htri : |f t - l| ≤ |f t - F n t| + |F n t - ln| + |ln - l| := by
    calc
      |f t - l| ≤ |f t - F n t| + |F n t - l| := abs_sub_le _ _ _
      _ ≤ |f t - F n t| + (|F n t - ln| + |ln - l|) :=
        add_le_add le_rfl (abs_sub_le (F n t) ln l)
      _ = _ := (add_assoc _ _ _).symm
  rw [abs_sub_comm (f t) (F n t)] at htri
  dsimp [δ] at hclose htclose
  linarith
