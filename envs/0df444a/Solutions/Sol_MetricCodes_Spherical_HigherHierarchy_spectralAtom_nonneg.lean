-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.spectralAtom_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.916513+00:00
-- url     : https://prove2.me/submissions/a416c5e4-096b-4ca9-9376-f6c746029ed4

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
open scoped BigOperators
open MetricCodes.Spherical.HigherHierarchy
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ spectralAtom u := by
  unfold spectralAtom quadraticCoordinate
  positivity
end MetricCodes.Spherical.HigherHierarchy
