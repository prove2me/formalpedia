-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.Phi_eq_sum_entropy_gaps
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:36.631864+00:00
-- url     : https://prove2.me/submissions/d4df0e71-c2cc-43d2-b27c-73b29a622410

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
open MetricCodes.Spherical.HigherHierarchy
noncomputable section
open Filter Topology
open scoped BigOperators Topology
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution {r : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ) :
    Phi a b =
      (∑ i : Fin r,
        (MetricCodes.sphericalEntropy (a i.castSucc) -
          MetricCodes.sphericalEntropy (b i))) +
        MetricCodes.sphericalEntropy (a (Fin.last r)) := by
  unfold Phi
  rw [Fin.sum_univ_castSucc]
  rw [Finset.sum_sub_distrib]
  ring
end MetricCodes.Spherical.HigherHierarchy
