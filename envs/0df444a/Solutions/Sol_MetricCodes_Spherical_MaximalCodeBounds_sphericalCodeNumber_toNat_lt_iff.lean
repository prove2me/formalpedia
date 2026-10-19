-- Prove2me | solution 1 for MetricCodes.Spherical.MaximalCodeBounds.sphericalCodeNumber_toNat_lt_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:36.631864+00:00
-- url     : https://prove2.me/submissions/9a58c7b2-abed-429a-b745-28f7878763d4

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_sphericalCodeNumber_lt_top
import Theorems.Thm_SpherePacking_sphericalCode_card_le_number
import Theorems.Thm_SpherePacking_sphericalCodeNumber_lt_top
import Theorems.Thm_MetricCodes_Spherical_MaximalCodeBounds_exists_sphericalCode_card_eq_number_toNat

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
open MetricCodes.Spherical.MaximalCodeBounds
namespace MetricCodes.Spherical.MaximalCodeBounds
theorem _root_.solution
    {n : ℕ} {s B : ℝ} (hs : s < 1) :
    ((SpherePacking.sphericalCodeNumber n s).toNat : ℝ) < B ↔
      ∀ C : SpherePacking.SphericalCode n s, (C.points.card : ℝ) < B := by
  constructor
  · intro h C
    have hnumber :
        ((SpherePacking.sphericalCodeNumber n s).toNat : ℕ∞) =
          SpherePacking.sphericalCodeNumber n s :=
      ENat.coe_toNat (ne_of_lt (SpherePacking.sphericalCodeNumber_lt_top hs))
    have hcard : C.points.card ≤
        (SpherePacking.sphericalCodeNumber n s).toNat := by
      exact_mod_cast hnumber.symm ▸ SpherePacking.sphericalCode_card_le_number C
    exact lt_of_le_of_lt (by exact_mod_cast hcard) h
  · intro h
    obtain ⟨C, hC⟩ := exists_sphericalCode_card_eq_number_toNat hs
    simpa only [hC] using h C
end MetricCodes.Spherical.MaximalCodeBounds
