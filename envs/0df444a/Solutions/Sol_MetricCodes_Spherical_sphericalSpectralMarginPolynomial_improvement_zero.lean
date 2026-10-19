-- Prove2me | solution 1 for MetricCodes.Spherical.sphericalSpectralMarginPolynomial_improvement_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.365393+00:00
-- url     : https://prove2.me/submissions/23d627d4-f324-4a43-af7d-23da594b61fc

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
theorem _root_.solution
    (a : ℝ) :
    sphericalSpectralMarginPolynomial a
      (sphericalImprovementSlope a) 0 =
      a * (1 + a) * (1 + 2 * a) := by
  unfold sphericalSpectralMarginPolynomial sphericalImprovementSlope
  ring
end MetricCodes.Spherical
