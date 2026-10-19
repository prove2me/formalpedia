-- Prove2me | solution 1 for MetricCodes.Johnson.combinedVariationalRate_le_hamming
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:30.299848+00:00
-- url     : https://prove2.me/submissions/e92b6303-c8b6-425c-827e-0cccb3bb3f49

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Johnson
noncomputable section
open scoped BigOperators InnerProductSpace Matrix
namespace MetricCodes.Johnson
theorem _root_.solution (δ : ℝ) :
    combinedVariationalRate δ ≤ MetricCodes.Hamming.variationalRate δ := by
  exact min_le_left _ _
end MetricCodes.Johnson
