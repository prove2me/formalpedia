-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.levelRate_at_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:37.685478+00:00
-- url     : https://prove2.me/submissions/b4f43d84-99cf-4751-9a9e-3db6df4d2381

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_sphericalEntropy_continuous
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_levelRate_le_levelRate_zero
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_levelRate_mono
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_levelRate_nonneg_all
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_eventually_levelRate_zero_le_squared_entropy

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
open Set Filter Topology
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution (r : ℕ) :
    levelRate r 0 = 0 := by
  have hsquare : Tendsto (fun t : ℝ => t ^ 2) (𝓝[>] 0) (nhds 0) := by
    simpa using
      ((tendsto_id : Tendsto (fun t : ℝ => t) (nhds 0) (nhds 0)).pow 2).mono_left
        (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  have hentropy : Tendsto
      (fun t : ℝ => MetricCodes.sphericalEntropy (t ^ 2))
      (𝓝[>] 0) (nhds 0) := by
    simpa [Function.comp_def, MetricCodes.sphericalEntropy] using
      (MetricCodes.Spherical.sphericalEntropy_continuous.continuousAt
        (x := (0 : ℝ))).tendsto.comp hsquare
  have hupper : ∀ᶠ t : ℝ in 𝓝[>] 0, t < 1 :=
    (tendsto_id.mono_left nhdsWithin_le_nhds).eventually
      (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hpositive : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t :=
    self_mem_nhdsWithin
  have hbound : ∀ᶠ t : ℝ in 𝓝[>] 0,
      levelRate r 0 ≤ MetricCodes.sphericalEntropy (t ^ 2) := by
    filter_upwards [eventually_levelRate_zero_le_squared_entropy,
      hpositive, hupper] with t hclassical ht ht'
    exact (levelRate_mono ht.le ht ht').trans
      ((levelRate_le_levelRate_zero ht ht').trans hclassical)
  exact le_antisymm (ge_of_tendsto hentropy hbound)
    (levelRate_nonneg_all r 0)
end MetricCodes.Spherical.HigherHierarchy
