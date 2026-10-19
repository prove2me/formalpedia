-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.CompactificationEntropy.entropy_gap_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:37.685478+00:00
-- url     : https://prove2.me/submissions/c7d03ef2-f7af-425d-a863-98df4482b987

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_sphericalEntropy_sub_nonneg

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
open Filter
open scoped BigOperators Topology
open MetricCodes.Spherical.HigherHierarchy.CompactificationEntropy
namespace MetricCodes.Spherical.HigherHierarchy.CompactificationEntropy
theorem _root_.solution {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) (i : Fin r) :
    0 ≤ MetricCodes.sphericalEntropy (a i.castSucc) -
      MetricCodes.sphericalEntropy (b i) :=
  MetricCodes.Spherical.sphericalEntropy_sub_nonneg
    (h.stabilizer_pos i).le (h.2 i).1.le
end MetricCodes.Spherical.HigherHierarchy.CompactificationEntropy
