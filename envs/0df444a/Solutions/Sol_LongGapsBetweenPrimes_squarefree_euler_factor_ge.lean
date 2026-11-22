-- Prove2me | solution 1 for LongGapsBetweenPrimes.squarefree_euler_factor_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:54:54.293094+00:00
-- url     : https://prove2.me/submissions/af078569-06b3-406e-8b2e-7bc596a78b44

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {p t : ℝ} (hp : 1 < p) (ht : 0 < t) :
    (1 - p ^ (-(1 + t)))⁻¹ ≤ 1 + p ^ (-t) / (p - 1) := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hpow : p ^ (-t) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hp (neg_neg_of_pos ht)
  have hden : 0 < 1 - p ^ (-(1 + t)) := sub_pos.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg hp (by linarith))
  rw [← one_div, div_le_iff₀ hden, neg_add, Real.rpow_add hp0, Real.rpow_neg_one]
  have hpm : 0 < p - 1 := sub_pos.mpr hp
  field_simp
  nlinarith [mul_nonneg (Real.rpow_nonneg hp0.le (-t)) (sub_nonneg.mpr hpow.le)]
end LongGapsBetweenPrimes
