-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyBoxPerron.exists_boxWidth_spectral_gap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:42.304385+00:00
-- url     : https://prove2.me/submissions/b013e243-adc3-474c-aa45-37eb54a14468

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyBoxPerron_boxWidth_ratio_tendsto

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
open scoped BigOperators InnerProductSpace Matrix Topology
open MetricCodes.Spherical.HigherHierarchyBoxPerron
open MetricCodes.Spherical.HigherHierarchy
open MetricCodes.Spherical.HigherHierarchyBoxSpectral
namespace MetricCodes.Spherical.HigherHierarchyBoxPerron
theorem _root_.solution
    {s gamma : ℝ} (hspectral : s < 2 * gamma) :
    ∃ m : ℕ, 0 < m ∧
      s < (2 * (m : ℝ) / (m + 1 : ℝ)) * gamma := by
  have htwo : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (nhds 2) :=
    tendsto_const_nhds
  have hfactor := (htwo.mul boxWidth_ratio_tendsto).mul_const gamma
  have hlimit :
      Tendsto (fun m : ℕ =>
        (2 * (m : ℝ) / (m + 1 : ℝ)) * gamma)
        atTop (nhds (2 * gamma)) := by
    convert hfactor using 1
    · ext m
      ring
    · ring_nf
  obtain ⟨m, hm, hpos⟩ :=
    ((hlimit.eventually (Ioi_mem_nhds hspectral)).and
      (eventually_gt_atTop (0 : ℕ))).exists
  exact ⟨m, hpos, hm⟩
end MetricCodes.Spherical.HigherHierarchyBoxPerron
