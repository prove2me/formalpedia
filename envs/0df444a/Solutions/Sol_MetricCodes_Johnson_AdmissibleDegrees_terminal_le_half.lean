-- Prove2me | solution 1 for MetricCodes.Johnson.AdmissibleDegrees.terminal_le_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:29.660979+00:00
-- url     : https://prove2.me/submissions/726f255b-cd7a-4f2c-b379-680d76392f26

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Johnson
noncomputable section
open scoped BigOperators InnerProductSpace Matrix
namespace MetricCodes.Johnson
namespace AdmissibleDegrees
theorem _root_.solution
    {n w p q L : ℕ} (h : AdmissibleDegrees n w p q L) :
    L ≤ n / 2 := by
  have hL := h.terminal_le_weight
  have hw := h.weight_half
  omega
end AdmissibleDegrees
end MetricCodes.Johnson
