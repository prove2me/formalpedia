-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.CompactificationEntropy.degree_ratio_lower_bound_of_entropy_gap_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:38.371954+00:00
-- url     : https://prove2.me/submissions/f36219da-1fa5-4845-a3cd-5c3370eac36e

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_CompactificationEntropy_shifted_degree_ratio_le_rpow_of_entropy_gap_le

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
open Filter
open scoped BigOperators Topology
open MetricCodes.Spherical.HigherHierarchy.CompactificationEntropy
namespace MetricCodes.Spherical.HigherHierarchy.CompactificationEntropy
theorem _root_.solution
    {a b C : ℝ} (hb : 1 ≤ b) (hba : b ≤ a)
    (hC : MetricCodes.sphericalEntropy a -
      MetricCodes.sphericalEntropy b ≤ C) :
    (2 * (2 : ℝ) ^ (C + 1 / Real.log 2))⁻¹ ≤ b / a := by
  have hb₀ : 0 < b := lt_of_lt_of_le (by norm_num) hb
  have ha : 0 < a := hb₀.trans_le hba
  let D : ℝ := (2 : ℝ) ^ (C + 1 / Real.log 2)
  have hD : 0 < D := Real.rpow_pos_of_pos (by norm_num) _
  have hratio : (1 + a) / (1 + b) ≤ D :=
    shifted_degree_ratio_le_rpow_of_entropy_gap_le hb₀ hba hC
  have hshift : 1 + a ≤ D * (1 + b) :=
    (div_le_iff₀ (by positivity : 0 < 1 + b)).mp hratio
  have hdouble : 1 + b ≤ 2 * b := by linarith
  have hbound : a ≤ (2 * D) * b := by
    have hmul := mul_le_mul_of_nonneg_left hdouble hD.le
    nlinarith
  apply (le_div_iff₀ ha).2
  calc
    (2 * D)⁻¹ * a = a / (2 * D) := by ring
    _ ≤ b := (div_le_iff₀ (by positivity : 0 < 2 * D)).mpr
      (by simpa [mul_comm, mul_left_comm, mul_assoc] using hbound)
end MetricCodes.Spherical.HigherHierarchy.CompactificationEntropy
