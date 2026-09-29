-- Prove2me | solution 1 for HlawkaSchatten.strictMono_signedPower
-- status  : ACCEPTED   (prove)
-- author  : @savarin
-- created : 2026-09-27T06:54:41.451071+00:00
-- url     : https://prove2.me/submissions/c411e15d-df1e-41ea-8f69-4aef255aaf21

import Definitions.Def_HlawkaSchatten_ScalarBregman
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Data.Sign.Basic
import Mathlib.Topology.Instances.Sign

open Filter
open scoped Topology

open HlawkaSchatten

theorem solution {q : ℝ} (hq : 0 < q) : StrictMono (signedPower q) := by
  intro x y hxy
  by_cases hx : x < 0
  · by_cases hy : y < 0
    · have hpow := Real.rpow_lt_rpow (neg_nonneg.mpr hy.le) (neg_lt_neg hxy) hq
      simp only [signedPower, sign_neg hx, sign_neg hy, SignType.coe_neg,
        SignType.coe_one, neg_mul, one_mul, abs_of_neg hx, abs_of_neg hy]
      linarith
    · have hy0 : 0 ≤ y := le_of_not_gt hy
      have hxpow : 0 < (-x) ^ q := Real.rpow_pos_of_pos (neg_pos.mpr hx) q
      simp only [signedPower, sign_neg hx, SignType.coe_neg, SignType.coe_one, neg_mul,
        one_mul, abs_of_neg hx]
      have hynonneg : 0 ≤ (SignType.sign y : ℝ) * |y| ^ q := by
        rcases hy0.eq_or_lt with rfl | hypos
        · simp
        · rw [sign_pos hypos]
          simp only [SignType.coe_one, one_mul]
          exact Real.rpow_nonneg (abs_nonneg y) q
      linarith
  · have hx0 : 0 ≤ x := le_of_not_gt hx
    have hy : 0 < y := hx0.trans_lt hxy
    rcases hx0.eq_or_lt with rfl | hxpos
    · simp only [signedPower, sign_zero, SignType.coe_zero, zero_mul, sign_pos hy,
        SignType.coe_one, one_mul]
      exact Real.rpow_pos_of_pos (abs_pos.mpr hy.ne') q
    · have hpow := Real.rpow_lt_rpow hxpos.le hxy hq
      simpa [signedPower, sign_pos hxpos, sign_pos hy, abs_of_pos hxpos, abs_of_pos hy]
        using hpow
