-- Prove2me | solution 1 for MetricCodes.Johnson.zero_fibre_spectral_algebra
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:29.660979+00:00
-- url     : https://prove2.me/submissions/ba350f56-8393-4fdc-8bdb-b480cc334407

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Johnson
noncomputable section
open scoped BigOperators InnerProductSpace Matrix
namespace MetricCodes.Johnson
theorem _root_.solution
    (z m s : ℝ)
    (hz : z ≠ 0) (hm : 1 - m ^ 2 ≠ 0)
    (hs : s ≠ 0) (hplus : 1 + 2 * s ≠ 0)
    (hsquare : 4 * s ^ 2 = 1 - z ^ 2) :
    1 -
        ((m - m * z ^ 2) ^ 2 /
          (z ^ 2 * (1 - m ^ 2) * (1 - z ^ 2)) +
          ((z ^ 2 - m ^ 2) * (1 - z ^ 2)) /
            (z ^ 2 * (1 - m ^ 2) * (2 * s))) =
      (z ^ 2 - m ^ 2) /
        ((1 - m ^ 2) * (1 + 2 * s)) := by
  have hzsq : z ^ 2 = 1 - 4 * s ^ 2 := by
    nlinarith [hsquare]
  have hzsqne : 1 - 4 * s ^ 2 ≠ 0 := by
    rw [← hzsq]
    exact pow_ne_zero 2 hz
  have hplus' : 2 * s + 1 ≠ 0 := by
    simpa [add_comm] using hplus
  have hplus'' : 1 + s * 2 ≠ 0 := by
    simpa [mul_comm] using hplus
  have hfour : 4 * s ^ 2 ≠ 0 := by
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hs)
  rw [hzsq]
  field_simp [hm, hs, hplus, hplus', hplus'', hfour, hzsqne]
  ; ring
end MetricCodes.Johnson
