-- Prove2me | solution 1 for MetricCodes.Boolean.hammingPositiveRadicalSymmetrization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:27.702855+00:00
-- url     : https://prove2.me/submissions/5e715533-54ea-4a40-8134-4f76dfc0b84d

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
noncomputable section
open scoped BigOperators Matrix
open MetricCodes.Boolean
variable {n : ℕ}
namespace MetricCodes.Boolean
theorem _root_.solution
    {d e a b N r : ℝ}
    (hd : 0 < d) (he : 0 < e)
    (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hcross : d * b = e * a) :
    (r / (N * a)) * Real.sqrt d =
      (r / (N * Real.sqrt (a * b))) * Real.sqrt e := by
  have hradical :
      Real.sqrt d * Real.sqrt b =
        Real.sqrt e * Real.sqrt a := by
    calc
      Real.sqrt d * Real.sqrt b = Real.sqrt (d * b) :=
        (Real.sqrt_mul hd.le b).symm
      _ = Real.sqrt (e * a) := by rw [hcross]
      _ = Real.sqrt e * Real.sqrt a :=
        Real.sqrt_mul he.le a
  have hsa : Real.sqrt a ≠ 0 := (Real.sqrt_pos.mpr ha).ne'
  have hsb : Real.sqrt b ≠ 0 := (Real.sqrt_pos.mpr hb).ne'
  calc
    (r / (N * a)) * Real.sqrt d =
        (r * Real.sqrt d) / (N * a) := by ring
    _ = (r * Real.sqrt e) /
          (N * (Real.sqrt a * Real.sqrt b)) := by
      apply (div_eq_div_iff
        (mul_ne_zero hN.ne' ha.ne')
        (mul_ne_zero hN.ne' (mul_ne_zero hsa hsb))).mpr
      calc
        (r * Real.sqrt d) *
            (N * (Real.sqrt a * Real.sqrt b)) =
          r * N * Real.sqrt a *
            (Real.sqrt d * Real.sqrt b) := by ring
        _ = r * N * Real.sqrt a *
            (Real.sqrt e * Real.sqrt a) := by rw [hradical]
        _ = (r * Real.sqrt e) *
            (N * (Real.sqrt a * Real.sqrt a)) := by ring
        _ = (r * Real.sqrt e) * (N * a) := by
          rw [Real.mul_self_sqrt ha.le]
    _ = (r / (N * Real.sqrt (a * b))) * Real.sqrt e := by
      rw [Real.sqrt_mul ha.le]
      ring
end MetricCodes.Boolean
