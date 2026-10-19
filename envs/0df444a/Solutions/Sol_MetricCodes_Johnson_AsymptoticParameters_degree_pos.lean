-- Prove2me | solution 1 for MetricCodes.Johnson.AsymptoticParameters.degree_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:29.660979+00:00
-- url     : https://prove2.me/submissions/2b6337af-2964-4b15-bc83-b945bfb5a5ca

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Johnson
noncomputable section
open scoped BigOperators InnerProductSpace Matrix
open MetricCodes.Johnson.AsymptoticParameters
variable {δ α β γ u : ℝ}
namespace MetricCodes.Johnson.AsymptoticParameters
theorem _root_.solution (h : AsymptoticParameters δ α β γ u) :
    0 < u := by
  nlinarith [h.support_nonneg, h.complement_nonneg,
    h.first_lt_degree]
end MetricCodes.Johnson.AsymptoticParameters
