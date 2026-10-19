-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.Entropy.limitingPackingExponent_sub_packingObjective_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:34.162962+00:00
-- url     : https://prove2.me/submissions/c4973097-7c7c-45bd-abcf-d1de5e9e9a58

import Theorems.Thm_CohnElkies_criticalBinaryExponent_eq_log_div
import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
open MeasureTheory ProbabilityTheory Real
open scoped ENNReal
open MetricCodes.Spherical.HigherHierarchy MetricCodes.Spherical.HigherHierarchy.Entropy
namespace MetricCodes.Spherical.HigherHierarchy.Entropy
theorem _root_.solution
    {Γ Φ Z : ℝ} (hZ : 0 < Z) (hΓ : Z = 1 - 2 * Γ) :
    limitingPackingExponent - packingObjective Γ Φ =
      (Real.log Real.pi - 1 + 2 * Real.log 2 * Φ + Real.log Z) /
        (2 * Real.log 2) := by
  have htwo : (2 : ℝ) ≠ 0 := by norm_num
  have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
  have hlog : Real.log (2 : ℝ) ≠ 0 :=
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  have hcritical :
      Real.log (2 * Real.pi / Real.exp 1) =
        Real.log 2 + Real.log Real.pi - 1 := by
    rw [Real.log_div (mul_ne_zero htwo hpi) (Real.exp_pos 1).ne',
      Real.log_mul htwo hpi, Real.log_exp]
  have hscale : Real.log (2 / Z) = Real.log 2 - Real.log Z := by
    rw [Real.log_div htwo hZ.ne']
  unfold limitingPackingExponent packingObjective
  rw [CohnElkies.criticalBinaryExponent_eq_log_div, ← hΓ, Real.logb, hcritical,
    hscale]
  field_simp
  ring
end MetricCodes.Spherical.HigherHierarchy.Entropy
