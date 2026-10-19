-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.lagrangeWeight_prepend_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:38.371954+00:00
-- url     : https://prove2.me/submissions/3e4f6a30-8316-410e-a167-7feac762f42d

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Interlacing_lagrangeDenominator_ne_zero
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_lagrangeNumerator_prepend_succ
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_lagrangeDenominator_prepend_succ

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
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHierarchy
noncomputable section
open Filter Topology
open scoped BigOperators Topology
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) (u v : ℝ) (i : Fin (r + 1))
    (hne : quadraticCoordinate (a i) - quadraticCoordinate u ≠ 0) :
    lagrangeWeight (prependAmbient u a) (prependStabilizer v b) i.succ =
      lagrangeWeight a b i *
        ((quadraticCoordinate (a i) - quadraticCoordinate v) /
          (quadraticCoordinate (a i) - quadraticCoordinate u)) := by
  unfold lagrangeWeight
  rw [lagrangeNumerator_prepend_succ, lagrangeDenominator_prepend_succ]
  field_simp [hne, h.lagrangeDenominator_ne_zero i]
end MetricCodes.Spherical.HigherHierarchy
