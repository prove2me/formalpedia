-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.levelRate_zero_eq_classical_of_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:39.667497+00:00
-- url     : https://prove2.me/submissions/30d1bc98-22bb-4cd2-ad54-cb15ffdaa416

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_sphericalEntropy_continuous
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_classical_le_levelRate_zero
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_levelRate_zero_le_entropy_of_classicalThreshold_lt

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
    {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    levelRate 0 s =
      MetricCodes.sphericalEntropy (MetricCodes.classicalThreshold s) := by
  apply le_antisymm
  · let a : ℕ → ℝ := fun n =>
      MetricCodes.classicalThreshold s + 1 / ((n : ℝ) + 1)
    have ha : Tendsto a atTop (nhds (MetricCodes.classicalThreshold s)) := by
      simpa [a] using
        (tendsto_const_nhds.add
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
    have hentropy : Tendsto
        (fun n => MetricCodes.sphericalEntropy (a n)) atTop
        (nhds (MetricCodes.sphericalEntropy (MetricCodes.classicalThreshold s))) :=
      MetricCodes.Spherical.sphericalEntropy_continuous.continuousAt.tendsto.comp ha
    apply ge_of_tendsto hentropy
    exact Filter.Eventually.of_forall fun n =>
      levelRate_zero_le_entropy_of_classicalThreshold_lt hs hs'
        (by
          dsimp [a]
          exact lt_add_of_pos_right _ (by positivity))
  · exact classical_le_levelRate_zero hs hs'
end MetricCodes.Spherical.HigherHierarchy
