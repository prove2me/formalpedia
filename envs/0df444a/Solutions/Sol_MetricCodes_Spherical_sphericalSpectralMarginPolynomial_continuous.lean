-- Prove2me | solution 1 for MetricCodes.Spherical.sphericalSpectralMarginPolynomial_continuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.365393+00:00
-- url     : https://prove2.me/submissions/35255240-1330-457d-8842-3d1d202e6922

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
theorem _root_.solution (a c : ℝ) :
    Continuous (sphericalSpectralMarginPolynomial a c) := by
  unfold sphericalSpectralMarginPolynomial
  fun_prop
end MetricCodes.Spherical
