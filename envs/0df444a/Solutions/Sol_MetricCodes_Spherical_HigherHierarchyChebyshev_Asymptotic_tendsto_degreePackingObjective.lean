-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyChebyshev.Asymptotic.tendsto_degreePackingObjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:34.162962+00:00
-- url     : https://prove2.me/submissions/d500cca3-7037-4a64-b0ee-e77de599d2f0

import Theorems.Thm_CohnElkies_criticalBinaryExponent_eq_log_div
import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_Asymptotic_tendsto_log_arcsin_correction
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_Asymptotic_tendsto_degree_ratio

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
open Filter
open scoped Topology BigOperators Interval
open MetricCodes.Spherical.HigherHierarchyChebyshev MetricCodes.Spherical.HigherHierarchyChebyshev.Asymptotic
namespace MetricCodes.Spherical.HigherHierarchyChebyshev.Asymptotic
theorem _root_.solution :
    Tendsto degreePackingObjective atTop
      (𝓝 CohnElkies.criticalBinaryExponent) := by
  have hlogratio :
      Tendsto (fun a : ℝ => Real.log ((1 + 2 * a) / (1 + a)))
        atTop (𝓝 (Real.log 2)) :=
    (Real.continuousAt_log (by norm_num : (2 : ℝ) ≠ 0)).tendsto.comp
      tendsto_degree_ratio
  have hentropy :
      Tendsto (fun a : ℝ => a * Real.log (1 + 1 / a)) atTop (𝓝 1) :=
    Real.tendsto_mul_log_one_add_div_atTop 1
  have hconstant : Tendsto (fun _ : ℝ => Real.log Real.pi) atTop
      (𝓝 (Real.log Real.pi)) := tendsto_const_nhds
  have hlimit :
      Tendsto (fun a : ℝ =>
        (Real.log Real.pi + Real.log ((1 + 2 * a) / (1 + a)) -
          a * Real.log (1 + 1 / a) -
          Real.log (Real.arcsin (1 / (1 + 2 * a)) /
            (1 / (1 + 2 * a)))) / (2 * Real.log 2)) atTop
        (𝓝 ((Real.log Real.pi + Real.log 2 - 1 - 0) /
          (2 * Real.log 2))) :=
    (((hconstant.add hlogratio).sub hentropy).sub
      tendsto_log_arcsin_correction).div_const (2 * Real.log 2)
  have hcritical :
      (Real.log Real.pi + Real.log 2 - 1 - 0) /
          (2 * Real.log 2) = CohnElkies.criticalBinaryExponent := by
    rw [CohnElkies.criticalBinaryExponent_eq_log_div,
      Real.log_div (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0)
        Real.pi_pos.ne') (Real.exp_pos 1).ne',
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) Real.pi_pos.ne',
      Real.log_exp]
    ring
  change Tendsto (fun a : ℝ =>
    (Real.log Real.pi + Real.log ((1 + 2 * a) / (1 + a)) -
      a * Real.log (1 + 1 / a) -
      Real.log (Real.arcsin (1 / (1 + 2 * a)) /
        (1 / (1 + 2 * a)))) / (2 * Real.log 2)) atTop
      (𝓝 CohnElkies.criticalBinaryExponent)
  rw [← hcritical]
  exact hlimit
end MetricCodes.Spherical.HigherHierarchyChebyshev.Asymptotic
