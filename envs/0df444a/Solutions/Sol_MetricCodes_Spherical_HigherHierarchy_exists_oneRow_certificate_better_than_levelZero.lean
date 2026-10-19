-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.exists_oneRow_certificate_better_than_levelZero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:36.631864+00:00
-- url     : https://prove2.me/submissions/cab4ea8e-5d95-4037-9be3-7a7e5941c566

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_Gamma_zero
import Theorems.Thm_MetricCodes_Spherical_sphericalImprovementSlope_gt_one
import Theorems.Thm_MetricCodes_Spherical_eventually_Gamma_improvement
import Theorems.Thm_MetricCodes_Spherical_eventually_sphericalEntropy_improvement
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Gamma_zero

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
open Filter Topology
open scoped Topology
open MetricCodes.Spherical.HigherHierarchy
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution
    {s a : ℝ} (ha : 0 < a)
    (hspectral : s < 2 * spectralAtom a) :
    ∃ A b : ℝ, 0 < b ∧ b < A ∧
      s < 2 * MetricCodes.Gamma A b ∧
      MetricCodes.sphericalEntropy A - MetricCodes.sphericalEntropy b <
        MetricCodes.sphericalEntropy a := by
  have hgamma := MetricCodes.Spherical.eventually_Gamma_improvement ha
  have hentropy := MetricCodes.Spherical.eventually_sphericalEntropy_improvement ha
  have hclassical : MetricCodes.Gamma a 0 = spectralAtom a := by
    simpa [spectralAtom, quadraticCoordinate] using
      (MetricCodes.Spherical.Gamma_zero ha)
  have hslope := MetricCodes.Spherical.sphericalImprovementSlope_gt_one ha
  have hgood :
      ∀ᶠ b : ℝ in 𝓝[>] 0,
        0 < b ∧
          b < MetricCodes.Spherical.sphericalImprovementPath a b ∧
          s < 2 * MetricCodes.Gamma
            (MetricCodes.Spherical.sphericalImprovementPath a b) b ∧
          MetricCodes.sphericalEntropy
              (MetricCodes.Spherical.sphericalImprovementPath a b) -
            MetricCodes.sphericalEntropy b < MetricCodes.sphericalEntropy a := by
    filter_upwards [hgamma, hentropy, self_mem_nhdsWithin]
      with b hγ hbentropy (hb : 0 < b)
    refine ⟨hb, ?_, ?_, hbentropy⟩
    · unfold MetricCodes.Spherical.sphericalImprovementPath
      nlinarith [mul_pos (sub_pos.mpr hslope) hb]
    · rw [hclassical] at hγ
      nlinarith
  obtain ⟨b, hb, hba, hgap, hcost⟩ := hgood.exists
  exact ⟨MetricCodes.Spherical.sphericalImprovementPath a b,
    b, hb, hba, hgap, hcost⟩
end MetricCodes.Spherical.HigherHierarchy
