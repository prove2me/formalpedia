-- Prove2me | solution 1 for Kyprianou.Ch01.fourierSeriesCompensatorAlgebra
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T05:33:23.650069+00:00
-- url     : https://prove2.me/submissions/aae5218a-eb2d-43fb-ac62-22f595814030

import Mathlib
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Group
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Complex
set_option autoImplicit false

/-! Exact manipulation of a compensated normalised absolutely convergent series. -/
theorem solution
    (a z : ℕ → ℂ) (ha : Summable a)
    (haz : Summable (fun n => a n * z n))
    (hmass : (∑' n, a n) = 1) (r : ℂ) :
    r * ((∑' n, a n * z n) - 1) =
      ∑' n, ((r * a n) * (z n - 1)) := by
  have hdifference :
      (∑' n, (a n * z n - a n)) =
        (∑' n, a n * z n) - (∑' n, a n) :=
    haz.tsum_sub ha
  calc
    r * ((∑' n, a n * z n) - 1)
        = r * ((∑' n, a n * z n) - (∑' n, a n)) := by rw [hmass]
    _ = r * (∑' n, (a n * z n - a n)) := by rw [hdifference]
    _ = ∑' n, (r * (a n * z n - a n)) := by rw [tsum_mul_left]
    _ = ∑' n, ((r * a n) * (z n - 1)) := by
      congr 1
      funext n
      ring
