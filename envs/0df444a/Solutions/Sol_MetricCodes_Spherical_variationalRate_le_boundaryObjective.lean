-- Prove2me | solution 1 for MetricCodes.Spherical.variationalRate_le_boundaryObjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:36.631864+00:00
-- url     : https://prove2.me/submissions/748abdca-7054-46f9-9c9a-6479c74e4d1f

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_classicalThreshold_pos
import Theorems.Thm_MetricCodes_Hamming_variationalRate_le_of_feasible
import Theorems.Thm_MetricCodes_Johnson_variationalRate_le_of_feasible
import Theorems.Thm_MetricCodes_Spherical_sphericalEntropy_continuous
import Theorems.Thm_MetricCodes_Spherical_variationalRate_le_of_feasible
import Theorems.Thm_MetricCodes_Spherical_boundaryDegree_pos
import Theorems.Thm_MetricCodes_Spherical_boundaryQuadratic_pos_iff_classicalThreshold_lt
import Theorems.Thm_MetricCodes_Spherical_feasible_iff_boundary

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
    {s a : ℝ} (hs : 0 < s) (hs' : s < 1)
    (hthreshold : MetricCodes.classicalThreshold s < a) :
    variationalRate s ≤
      MetricCodes.sphericalEntropy a -
        MetricCodes.sphericalEntropy (boundaryDegree s a) := by
  have ha := (MetricCodes.classicalThreshold_pos hs hs').trans hthreshold
  have hquadratic :=
    (boundaryQuadratic_pos_iff_classicalThreshold_lt
      hs hs' ha).mpr hthreshold
  have hpositive := boundaryDegree_pos hquadratic
  let endpoint : ℝ := boundaryDegree s a
  let F : Filter ℝ := 𝓝[<] endpoint
  have hlimit :
      Tendsto
        (fun b : ℝ =>
          MetricCodes.sphericalEntropy a - MetricCodes.sphericalEntropy b)
        F (𝓝 (MetricCodes.sphericalEntropy a -
          MetricCodes.sphericalEntropy endpoint)) := by
    have hcontinuous : Continuous
        (fun b : ℝ =>
          MetricCodes.sphericalEntropy a - MetricCodes.sphericalEntropy b) :=
      continuous_const.sub sphericalEntropy_continuous
    exact hcontinuous.continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  have hbound :
      ∀ᶠ b : ℝ in F,
        variationalRate s ≤
          MetricCodes.sphericalEntropy a - MetricCodes.sphericalEntropy b := by
    have hpos : ∀ᶠ b : ℝ in F, 0 < b :=
      nhdsWithin_le_nhds (lt_mem_nhds hpositive)
    filter_upwards [hpos, self_mem_nhdsWithin]
      with b hb (hupper : b < endpoint)
    apply variationalRate_le_of_feasible
    apply (feasible_iff_boundary hs hs').mpr
    exact ⟨hthreshold, hb, hupper⟩
  exact ge_of_tendsto hlimit hbound
end MetricCodes.Spherical
