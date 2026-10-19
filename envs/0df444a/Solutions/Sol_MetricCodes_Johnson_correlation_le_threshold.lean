-- Prove2me | solution 1 for MetricCodes.Johnson.correlation_le_threshold
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:29.660979+00:00
-- url     : https://prove2.me/submissions/e12fb445-e9e0-4fd3-b260-5c3ebc760da1

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Johnson_correlation_eq_hamming

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Johnson
noncomputable section
open scoped BigOperators InnerProductSpace Matrix
namespace MetricCodes.Johnson
theorem _root_.solution {n w d : ℕ}
    (hw : 0 < w) (hwn : w < n)
    {x y : JohnsonSphere n w}
    (hd : d ≤ MetricCodes.hammingDist (x : BinaryWord n) (y : BinaryWord n)) :
    correlation x y ≤ threshold n w d := by
  rw [correlation_eq_hamming hw hwn x y]
  have hcomp : 0 < n - w := Nat.sub_pos_of_lt hwn
  have hden : 0 < 2 * (w : ℝ) * ((n - w : ℕ) : ℝ) := by
    positivity
  have hd' : (d : ℝ) ≤
      (MetricCodes.hammingDist (x : BinaryWord n) (y : BinaryWord n) : ℝ) := by
    exact_mod_cast hd
  have hnum :
      (n : ℝ) * (d : ℝ) ≤
        (n : ℝ) *
          (MetricCodes.hammingDist (x : BinaryWord n) (y : BinaryWord n) : ℝ) :=
    mul_le_mul_of_nonneg_left hd' (Nat.cast_nonneg n)
  have hfrac :=
    (div_le_div_iff_of_pos_right hden).mpr hnum
  unfold threshold
  linarith
end MetricCodes.Johnson
