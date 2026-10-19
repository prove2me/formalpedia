-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.Weyl.flooredWeight_antitone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:41.063146+00:00
-- url     : https://prove2.me/submissions/da877309-7e61-4588-aec8-3e9b3257cc2c

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
open MetricCodes
open MetricCodes.Spherical
noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped BigOperators Nat Topology
open MetricCodes.Spherical.HigherHierarchy MetricCodes.Spherical.HigherHierarchy.Weyl
namespace MetricCodes.Spherical.HigherHierarchy.Weyl
theorem _root_.solution {r : ℕ}
    {a : Fin (r + 1) → ℝ} (ha : Antitone a) (n : ℕ) :
    Antitone (flooredWeight a n) := by
  intro i j hij
  unfold flooredWeight
  exact Nat.floor_mono
    (mul_le_mul_of_nonneg_right (ha hij) (Nat.cast_nonneg n))
end MetricCodes.Spherical.HigherHierarchy.Weyl
