-- Prove2me | solution 1 for MetricCodes.Hamming.spectralMarginPolynomial_factor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:28.946406+00:00
-- url     : https://prove2.me/submissions/5a7c5b13-2058-46dd-86da-fcdf8fc9bc9e

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
noncomputable section
set_option autoImplicit false
open Filter Metric Topology
open scoped BigOperators InnerProductSpace Topology
open MetricCodes.Hamming
namespace MetricCodes.Hamming
theorem _root_.solution (a c b : ℝ) :
    ((a + c * b - b) * (1 - (a + c * b) - b)) ^ 2 -
      (a * (1 - a)) * ((a + c * b) * (1 - (a + c * b))) =
        b * spectralMarginPolynomial a c b := by
  unfold spectralMarginPolynomial
  ring
end MetricCodes.Hamming
