-- Prove2me | solution 1 for MetricCodes.Spherical.sphericalSpectralMarginPolynomial_factor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.365393+00:00
-- url     : https://prove2.me/submissions/41ebd5fe-1a6c-4656-8170-563ac638aa3f

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
open Filter Topology
open scoped Topology
namespace MetricCodes.Spherical
theorem _root_.solution (a c b : ℝ) :
    (((a + c * b) * (1 + (a + c * b)) - b * (1 + b)) *
        (1 + 2 * a)) ^ 2 -
      a * (1 + a) * (1 + 2 * (a + c * b)) ^ 2 *
        ((a + c * b) * (1 + (a + c * b))) =
      b * sphericalSpectralMarginPolynomial a c b := by
  unfold sphericalSpectralMarginPolynomial
  ring
end MetricCodes.Spherical
