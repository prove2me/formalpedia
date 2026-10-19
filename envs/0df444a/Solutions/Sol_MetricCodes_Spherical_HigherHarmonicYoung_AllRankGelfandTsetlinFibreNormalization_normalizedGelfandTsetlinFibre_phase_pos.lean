-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinFibreNormalization.normalizedGelfandTsetlinFibre_phase_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:42.304385+00:00
-- url     : https://prove2.me/submissions/d2df29c2-8bad-496c-acf8-2c035e079d06

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

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
set_option autoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option autoImplicit false
set_option maxHeartbeats 1800000
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHarmonicYoung
noncomputable section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 80000
open scoped BigOperators InnerProductSpace
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinFibreNormalization
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankGelfandTsetlinHarmonicIsometry
open MetricCodes.Spherical.HigherRepresentationGraph
open SpherePacking.HarmonicCoordinateOperators
namespace MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinFibreNormalization
theorem _root_.solution
    {c : ℝ} (hc : 0 < c) :
    0 < (Real.sqrt c)⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr hc)
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinFibreNormalization
