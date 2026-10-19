-- Prove2me | solution 1 for MetricCodes.Johnson.correlation_eq_hamming
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:29.660979+00:00
-- url     : https://prove2.me/submissions/05213738-a34e-427d-8095-68c04a64aa78

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_hammingDist_eq_two_mul_johnsonDist

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Johnson
noncomputable section
open scoped BigOperators InnerProductSpace Matrix
namespace MetricCodes.Johnson
theorem _root_.solution {n w : ℕ}
    (hw : 0 < w) (hwn : w < n) (x y : JohnsonSphere n w) :
    correlation x y =
      1 - (n : ℝ) *
        (MetricCodes.hammingDist (x : BinaryWord n) (y : BinaryWord n) : ℝ) /
          (2 * (w : ℝ) * ((n - w : ℕ) : ℝ)) := by
  have hw' : (w : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hw
  have hcomp : 0 < n - w := Nat.sub_pos_of_lt hwn
  have hcomp' : ((n - w : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hcomp
  rw [MetricCodes.hammingDist_eq_two_mul_johnsonDist]
  push_cast
  unfold correlation
  field_simp [hw', hcomp']
end MetricCodes.Johnson
