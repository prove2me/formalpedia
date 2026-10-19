-- Prove2me | solution 1 for MetricCodes.Johnson.threshold_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:29.660979+00:00
-- url     : https://prove2.me/submissions/112d171b-0e2f-489f-b542-51f67304e7b6

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Johnson
noncomputable section
open scoped BigOperators InnerProductSpace Matrix
namespace MetricCodes.Johnson
theorem _root_.solution {n w d : ℕ}
    (hw : 0 < w) (hwn : w < n) (hd : 0 < d) :
    threshold n w d < 1 := by
  have hn : 0 < n := by omega
  have hcomp : 0 < n - w := Nat.sub_pos_of_lt hwn
  have hnum : 0 < (n : ℝ) * (d : ℝ) := by positivity
  have hden : 0 < 2 * (w : ℝ) * ((n - w : ℕ) : ℝ) := by
    positivity
  unfold threshold
  have hfrac := div_pos hnum hden
  linarith
end MetricCodes.Johnson
