-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.classicalThreshold_entropy_lt_half_neg_logb
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:39.667497+00:00
-- url     : https://prove2.me/submissions/7ecf9544-1869-4d9b-a526-93cf491ba4d2

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_sphericalEntropy_eq_log_add
import Theorems.Thm_MetricCodes_classicalThreshold_pos
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_log_inv_lt_half_inv_sub_self
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_lt_log_one_add_add_half_log_one_add_sq

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
set_option maxHeartbeats 2000000
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution
    {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    MetricCodes.sphericalEntropy (MetricCodes.classicalThreshold s) <
      -(1 / 2 : ℝ) * Real.logb 2 (1 - s) := by
  let u : ℝ := Real.sqrt (1 - s ^ 2)
  let t : ℝ := s / (1 + u)
  let a : ℝ := MetricCodes.classicalThreshold s
  have hrad : 0 < 1 - s ^ 2 := by nlinarith
  have hu : 0 < u := Real.sqrt_pos.mpr hrad
  have hu_sq : u ^ 2 = 1 - s ^ 2 := Real.sq_sqrt hrad.le
  have ht : 0 < t := by dsimp [t]; positivity
  have ht' : t < 1 := by
    dsimp [t]
    apply (div_lt_one (by positivity)).mpr
    linarith
  have htden : 0 < 1 - t ^ 2 := by nlinarith
  have hsparam : s = 2 * t / (1 + t ^ 2) := by
    dsimp [t]
    field_simp
    nlinarith [hu_sq]
  have ha : 0 < a := MetricCodes.classicalThreshold_pos hs hs'
  have ht_sq : t ^ 2 = (1 - u) / (1 + u) := by
    dsimp [t]
    field_simp
    nlinarith [hu_sq]
  have haparam : a = t ^ 2 / (1 - t ^ 2) := by
    change (1 / u - 1) / 2 = t ^ 2 / (1 - t ^ 2)
    rw [ht_sq]
    field_simp [hu.ne', (by positivity : 1 + u ≠ 0)]
    ring
  have hones : 1 - s = (1 - t) ^ 2 / (1 + t ^ 2) := by
    rw [hsparam]
    field_simp
    ring
  have honea : 1 + a = 1 / (1 - t ^ 2) := by
    rw [haparam]
    field_simp [htden.ne']
    ring
  have hratio : (1 + a) / a = (1 / t) ^ 2 := by
    rw [haparam]
    field_simp [ht.ne', htden.ne']
    ring
  have hlogtwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hentropy :
      Real.log 2 * MetricCodes.sphericalEntropy a =
        Real.log (1 + a) + a * Real.log ((1 + a) / a) := by
    rw [MetricCodes.sphericalEntropy_eq_log_add ha]
    unfold Real.logb
    field_simp [hlogtwo.ne']
  have hlogones :
      Real.log (1 - s) =
        2 * Real.log (1 - t) - Real.log (1 + t ^ 2) := by
    rw [hones, Real.log_div (by positivity) (by positivity),
      Real.log_pow]
    norm_num
  have hlogonea :
      Real.log (1 + a) =
        -(Real.log (1 - t) + Real.log (1 + t)) := by
    rw [honea, one_div, Real.log_inv]
    have hfactor : 1 - t ^ 2 = (1 - t) * (1 + t) := by ring
    rw [hfactor, Real.log_mul (by linarith) (by linarith)]
  have hlogratio :
      Real.log ((1 + a) / a) = 2 * Real.log (1 / t) := by
    rw [hratio, Real.log_pow]
    norm_num
  have hfirst :
      t < Real.log (1 + t) +
        (1 / 2 : ℝ) * Real.log (1 + t ^ 2) :=
    lt_log_one_add_add_half_log_one_add_sq ht ht'
  have hlast :
      2 * t ^ 2 / (1 - t ^ 2) * Real.log (1 / t) < t := by
    have hcoefficient : 0 < 2 * t ^ 2 / (1 - t ^ 2) := by positivity
    calc
      2 * t ^ 2 / (1 - t ^ 2) * Real.log (1 / t) <
          2 * t ^ 2 / (1 - t ^ 2) * ((1 / t - t) / 2) :=
        mul_lt_mul_of_pos_left (log_inv_lt_half_inv_sub_self ht ht')
          hcoefficient
      _ = t := by
        field_simp [ht.ne', htden.ne']
  have hgap : 0 < Real.log (1 + t) +
      (1 / 2 : ℝ) * Real.log (1 + t ^ 2) -
        2 * t ^ 2 / (1 - t ^ 2) * Real.log (1 / t) := by
    linarith
  have hidentity :
      Real.log 2 *
          (-(1 / 2 : ℝ) * Real.logb 2 (1 - s) -
            MetricCodes.sphericalEntropy a) =
        Real.log (1 + t) +
          (1 / 2 : ℝ) * Real.log (1 + t ^ 2) -
            2 * t ^ 2 / (1 - t ^ 2) * Real.log (1 / t) := by
    calc
      _ = -(1 / 2 : ℝ) * Real.log (1 - s) -
          Real.log 2 * MetricCodes.sphericalEntropy a := by
        unfold Real.logb
        field_simp [hlogtwo.ne']
      _ = -(1 / 2 : ℝ) * Real.log (1 - s) -
          (Real.log (1 + a) + a * Real.log ((1 + a) / a)) := by
        rw [hentropy]
      _ = _ := by
        rw [hlogones, hlogonea, hlogratio, haparam]
        ring
  have hpositive :
      0 < -(1 / 2 : ℝ) * Real.logb 2 (1 - s) -
        MetricCodes.sphericalEntropy a := by
    apply (mul_pos_iff_of_pos_left hlogtwo).mp
    rw [hidentity]
    exact hgap
  exact sub_pos.mp hpositive
end MetricCodes.Spherical.HigherHierarchy
