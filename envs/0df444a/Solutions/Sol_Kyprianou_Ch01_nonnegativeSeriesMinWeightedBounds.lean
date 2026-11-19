-- Prove2me | solution 1 for Kyprianou.Ch01.nonnegativeSeriesMinWeightedBounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T10:06:29.718133+00:00
-- url     : https://prove2.me/submissions/ad374b24-077d-4cdf-b4d7-55fbc948ee78

import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Tactic.Linarith
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped BigOperators
set_option autoImplicit false

/-- A bounded weighting can lose no more than the unweighted residual mass. -/
theorem solution (a b w : ℕ → ℝ)
    (ha : ∀ k, 0 ≤ a k) (hasum : Summable a)
    (hb : ∀ k, 0 ≤ b k) (hbsum : Summable b)
    (hw : ∀ k, 0 ≤ w k ∧ w k ≤ 1) :
    (∑' k, min (a k) (b k) * w k) ≤
      (∑' k, a k * w k) ∧
    (∑' k, a k * w k) ≤
      (∑' k, min (a k) (b k) * w k) +
        (∑' k, a k) - (∑' k, min (a k) (b k)) := by
  have hm0 (k : ℕ) : 0 ≤ min (a k) (b k) :=
    le_min (ha k) (hb k)
  have hm : Summable (fun k => min (a k) (b k)) :=
    hbsum.of_nonneg_of_le hm0 (fun k => min_le_right _ _)
  have haw : Summable (fun k => a k * w k) :=
    hasum.of_nonneg_of_le
      (fun k => mul_nonneg (ha k) (hw k).1)
      (fun k => by simpa using
        (mul_le_mul_of_nonneg_left (hw k).2 (ha k)))
  have hmw : Summable (fun k => min (a k) (b k) * w k) :=
    hm.of_nonneg_of_le
      (fun k => mul_nonneg (hm0 k) (hw k).1)
      (fun k => by simpa using
        (mul_le_mul_of_nonneg_left (hw k).2 (hm0 k)))
  constructor
  · exact hmw.tsum_le_tsum (fun k =>
      mul_le_mul_of_nonneg_right (min_le_left _ _) (hw k).1) haw
  · have hres := (haw.sub hmw).tsum_le_tsum
      (fun k => by
        have hp : 0 ≤ a k - min (a k) (b k) :=
          sub_nonneg.mpr (min_le_left _ _)
        have he : a k * w k - min (a k) (b k) * w k =
            (a k - min (a k) (b k)) * w k := by ring
        rw [he]
        simpa using (mul_le_mul_of_nonneg_left (hw k).2 hp))
      (hasum.sub hm)
    rw [haw.tsum_sub hmw, hasum.tsum_sub hm] at hres
    linarith
