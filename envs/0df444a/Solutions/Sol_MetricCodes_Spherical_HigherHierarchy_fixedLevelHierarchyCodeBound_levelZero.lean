-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.fixedLevelHierarchyCodeBound_levelZero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:42.304385+00:00
-- url     : https://prove2.me/submissions/1a789ec3-0ca5-4d3e-a2d7-d797be1c4fdb

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_eventually_sphericalCode_card_lt_levelZero

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
open Filter Topology
open scoped BigOperators InnerProductSpace Matrix Topology
open MetricCodes.Spherical.HigherProjectionInstantiation
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution
    {s R : ℝ} (hs : 0 < s) (hs' : s < 1)
    (a : Fin 1 → ℝ) (b : Fin 0 → ℝ)
    (hinterlacing : Interlacing a b)
    (hspectral : s < 2 * Gamma a b)
    (hR : Phi a b < R) :
    ∀ᶠ n : ℕ in atTop, ∀ C : SpherePacking.SphericalCode n s,
      (C.points.card : ℝ) < (2 : ℝ) ^ (R * (n : ℝ)) := by
  filter_upwards [eventually_sphericalCode_card_lt_levelZero
    hs hs' a b hinterlacing hspectral, eventually_gt_atTop (0 : ℕ)]
    with n hn hnpos
  intro C
  refine (hn C).trans ?_
  apply Real.strictMono_rpow_of_base_gt_one (by norm_num : (1 : ℝ) < 2)
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hnpos
  nlinarith [mul_pos (sub_pos.mpr hR) hnreal]
end MetricCodes.Spherical.HigherHierarchy
