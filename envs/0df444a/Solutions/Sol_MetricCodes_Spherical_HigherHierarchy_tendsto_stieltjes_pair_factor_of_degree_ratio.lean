-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.tendsto_stieltjes_pair_factor_of_degree_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:38.99809+00:00
-- url     : https://prove2.me/submissions/9eac87f4-742b-4d03-8483-4de4e524ba06

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_tendsto_quadratic_residue_ratio_of_degree_ratio

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
set_option autoImplicit false
set_option maxHeartbeats 4000000
open Filter Topology
open scoped BigOperators Topology
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution
    {u v : ℕ → ℝ} {d : ℝ}
    (hu : Tendsto u atTop atTop)
    (hd : Tendsto (fun n => v n / u n) atTop (𝓝 d))
    (t : ℝ) :
    Tendsto
      (fun n =>
        (t + quadraticCoordinate (v n)) /
          (t + quadraticCoordinate (u n)))
      atTop (𝓝 (d ^ 2)) := by
  have hlimit :=
    tendsto_quadratic_residue_ratio_of_degree_ratio hu hd (-t)
  apply hlimit.congr'
  filter_upwards [] with n
  rw [show -t - quadraticCoordinate (v n) =
      -(t + quadraticCoordinate (v n)) by ring,
    show -t - quadraticCoordinate (u n) =
      -(t + quadraticCoordinate (u n)) by ring]
  exact neg_div_neg_eq _ _
end MetricCodes.Spherical.HigherHierarchy
