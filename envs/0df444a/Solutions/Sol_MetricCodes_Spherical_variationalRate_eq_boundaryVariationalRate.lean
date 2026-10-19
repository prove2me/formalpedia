-- Prove2me | solution 1 for MetricCodes.Spherical.variationalRate_eq_boundaryVariationalRate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:36.631864+00:00
-- url     : https://prove2.me/submissions/e6187867-22b0-4571-8f46-907178c021e2

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_rateSet_nonempty_of_interior
import Theorems.Thm_MetricCodes_Johnson_Rate_rateSet_nonempty_of_interior
import Theorems.Thm_MetricCodes_Spherical_sphericalEntropy_strictMono
import Theorems.Thm_MetricCodes_Spherical_boundaryDegree_pos
import Theorems.Thm_MetricCodes_Spherical_rateSet_nonempty_of_interior
import Theorems.Thm_MetricCodes_Spherical_boundaryQuadratic_pos_iff_classicalThreshold_lt
import Theorems.Thm_MetricCodes_Spherical_feasible_iff_boundary
import Theorems.Thm_MetricCodes_Spherical_boundaryRateSet_bddBelow
import Theorems.Thm_MetricCodes_Spherical_variationalRate_le_boundaryObjective

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
open scoped Topology
namespace MetricCodes.Spherical
theorem _root_.solution
    {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    variationalRate s = boundaryVariationalRate s := by
  have hnonempty := rateSet_nonempty_of_interior hs hs'
  apply le_antisymm
  · unfold boundaryVariationalRate
    apply le_csInf
    · obtain ⟨r, a, b, hfeasible, hr⟩ := hnonempty
      have hdomain := (feasible_iff_boundary hs hs').mp hfeasible
      exact ⟨MetricCodes.sphericalEntropy a -
        MetricCodes.sphericalEntropy (boundaryDegree s a),
        a, hdomain.1, rfl⟩
    · rintro r ⟨a, hthreshold, rfl⟩
      exact variationalRate_le_boundaryObjective hs hs' hthreshold
  · unfold variationalRate
    apply le_csInf hnonempty
    rintro r ⟨a, b, hfeasible, rfl⟩
    have hdomain := (feasible_iff_boundary hs hs').mp hfeasible
    have ha : 0 < a := hfeasible.1.trans hfeasible.2.1
    have hquadratic :=
      (boundaryQuadratic_pos_iff_classicalThreshold_lt
        hs hs' ha).mpr hdomain.1
    calc
      boundaryVariationalRate s ≤
          MetricCodes.sphericalEntropy a -
            MetricCodes.sphericalEntropy (boundaryDegree s a) := by
        exact csInf_le (boundaryRateSet_bddBelow hs hs')
          ⟨a, hdomain.1, rfl⟩
      _ ≤ MetricCodes.sphericalEntropy a - MetricCodes.sphericalEntropy b := by
        apply sub_le_sub_left
        exact sphericalEntropy_strictMono.monotoneOn
          hdomain.2.1.le
          (boundaryDegree_pos hquadratic).le
          hdomain.2.2.le
end MetricCodes.Spherical
