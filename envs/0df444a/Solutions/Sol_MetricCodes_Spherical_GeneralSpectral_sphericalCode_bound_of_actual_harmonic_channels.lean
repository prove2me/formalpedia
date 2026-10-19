-- Prove2me | solution 1 for MetricCodes.Spherical.GeneralSpectral.sphericalCode_bound_of_actual_harmonic_channels
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:36.020426+00:00
-- url     : https://prove2.me/submissions/01f1e7d9-d927-411c-9e7c-1a1f47221583

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_SpherePacking_HarmonicCoordinateChannels_sphericalCode_bound_of_sourceSpectralRow

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
open Filter Topology
open scoped BigOperators Nat Topology InnerProductSpace
open MetricCodes.Spherical.GeneralSpectral
namespace MetricCodes.Spherical.GeneralSpectral
theorem _root_.solution
    {n k L : ℕ} (hn : 3 ≤ n) (hkl : k < L)
    {s : ℝ} (hs : s ≤ 1)
    (hgap : s < SpherePacking.Jacobi.topEigenvalue n k L)
    (C : SpherePacking.SphericalCode n s) :
    (C.points.card : ℝ) ≤
      ((1 - s) /
        (SpherePacking.Jacobi.topEigenvalue n k L - s)) *
        ((SpherePacking.truncatedHarmonicDimension n k L : ℝ) /
          (SpherePacking.Gegenbauer.fibreDimension n k : ℝ)) := by
  exact
    SpherePacking.HarmonicCoordinateChannels.sphericalCode_bound_of_sourceSpectralRow
      hn hkl.le
      (SpherePacking.harmonicDegreeFibre hn k L)
      (SpherePacking.HarmonicCoordinateChannels.sourceSpectralRowDataOfAdjacent
        hn hkl (SpherePacking.harmonicDegreeFibre hn k L)
        (SpherePacking.HarmonicAdjacentChannelTransport.actualSourceAdjacentChannelData
          hn k L))
      hs hgap C
end MetricCodes.Spherical.GeneralSpectral
