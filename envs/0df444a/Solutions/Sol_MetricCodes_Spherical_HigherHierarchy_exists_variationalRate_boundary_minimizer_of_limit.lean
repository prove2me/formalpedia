-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.exists_variationalRate_boundary_minimizer_of_limit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:39.667497+00:00
-- url     : https://prove2.me/submissions/7b05e1ea-92e4-4ca0-af12-8f9fffa5f83a

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_sphericalEntropy_strictMono
import Theorems.Thm_MetricCodes_Spherical_exists_strict_improving_spherical_feasible
import Theorems.Thm_MetricCodes_Spherical_boundaryDegree_pos
import Theorems.Thm_MetricCodes_Spherical_boundaryQuadratic_pos_iff_classicalThreshold_lt
import Theorems.Thm_MetricCodes_Spherical_feasible_iff_boundary
import Theorems.Thm_MetricCodes_Spherical_boundaryRateSet_bddBelow
import Theorems.Thm_MetricCodes_Spherical_variationalRate_eq_boundaryVariationalRate
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_oneRowBoundaryObjective_continuous
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_oneRowBoundaryObjective_classicalThreshold

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
open scoped Topology
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution
    {s L : ℝ} (hs : 0 < s) (hs' : s < 1)
    (hlimit : Tendsto (fun a : ℝ => oneRowBoundaryObjective s a)
      atTop (𝓝 L))
    (hendpoint :
      MetricCodes.sphericalEntropy (MetricCodes.classicalThreshold s) < L) :
    ∃ a : ℝ, MetricCodes.classicalThreshold s < a ∧
      MetricCodes.Spherical.variationalRate s = oneRowBoundaryObjective s a ∧
      ∀ t : ℝ, MetricCodes.classicalThreshold s < t →
        oneRowBoundaryObjective s a ≤ oneRowBoundaryObjective s t := by
  obtain ⟨u, b, hfeasible, himprove⟩ :=
    MetricCodes.Spherical.exists_strict_improving_spherical_feasible hs hs'
  have hdomain :=
    (MetricCodes.Spherical.feasible_iff_boundary hs hs').mp hfeasible
  have hu : 0 < u := hfeasible.1.trans hfeasible.2.1
  have hquadratic :=
    (MetricCodes.Spherical.boundaryQuadratic_pos_iff_classicalThreshold_lt
      hs hs' hu).mpr hdomain.1
  have hboundary :
      MetricCodes.sphericalEntropy b ≤
        MetricCodes.sphericalEntropy
          (MetricCodes.Spherical.boundaryDegree s u) :=
    MetricCodes.Spherical.sphericalEntropy_strictMono.monotoneOn
      hdomain.2.1.le
      (MetricCodes.Spherical.boundaryDegree_pos hquadratic).le
      hdomain.2.2.le
  have hgood :
      oneRowBoundaryObjective s u <
        MetricCodes.sphericalEntropy (MetricCodes.classicalThreshold s) := by
    unfold oneRowBoundaryObjective
    linarith
  have hgood_limit : oneRowBoundaryObjective s u < L :=
    hgood.trans hendpoint
  obtain ⟨A, hA⟩ :=
    (eventually_atTop.1 (hlimit.eventually (lt_mem_nhds hgood_limit)))
  let T : ℝ := max A u
  have hT : MetricCodes.classicalThreshold s ≤ T :=
    hdomain.1.le.trans (le_max_right A u)
  obtain ⟨a, ha, hmin⟩ :=
    isCompact_Icc.exists_isMinOn
      (Set.nonempty_Icc.mpr hT)
      (oneRowBoundaryObjective_continuous s).continuousOn
  have hau :
      oneRowBoundaryObjective s a ≤ oneRowBoundaryObjective s u :=
    hmin ⟨hdomain.1.le, le_max_right A u⟩
  have haclassical :
      oneRowBoundaryObjective s a <
        MetricCodes.sphericalEntropy (MetricCodes.classicalThreshold s) :=
    hau.trans_lt hgood
  have hastrict : MetricCodes.classicalThreshold s < a := by
    by_contra hnot
    have heq : a = MetricCodes.classicalThreshold s :=
      le_antisymm (le_of_not_gt hnot) ha.1
    rw [heq, oneRowBoundaryObjective_classicalThreshold hs hs'] at haclassical
    exact (lt_irrefl _) haclassical
  have hglobal : ∀ t : ℝ, MetricCodes.classicalThreshold s < t →
      oneRowBoundaryObjective s a ≤ oneRowBoundaryObjective s t := by
    intro t ht
    by_cases htT : t ≤ T
    · exact hmin ⟨ht.le, htT⟩
    · have htail : oneRowBoundaryObjective s u <
          oneRowBoundaryObjective s t :=
        hA t ((le_max_left A u).trans (le_of_not_ge htT))
      exact hau.trans htail.le
  refine ⟨a, hastrict, ?_, hglobal⟩
  rw [MetricCodes.Spherical.variationalRate_eq_boundaryVariationalRate hs hs']
  unfold MetricCodes.Spherical.boundaryVariationalRate
  apply le_antisymm
  · exact csInf_le (MetricCodes.Spherical.boundaryRateSet_bddBelow hs hs')
      ⟨a, hastrict, rfl⟩
  · refine le_csInf (s := MetricCodes.Spherical.boundaryRateSet s) ?_ ?_
    · exact ⟨oneRowBoundaryObjective s a, a, hastrict, rfl⟩
    · rintro _ ⟨t, ht, rfl⟩
      exact hglobal t ht
end MetricCodes.Spherical.HigherHierarchy
