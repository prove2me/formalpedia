-- Prove2me | solution 1 for OAI.Problem356.CenterCertificate.strict_of_not_good
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T21:17:59.142204+00:00
-- url     : https://prove2.me/submissions/4a115153-fa2c-435a-ac9c-a1af0e881183

import Mathlib
import Definitions.Def_CoulombCounterexample
import Definitions.Def_OAI_Analysis_CoulombTransport_AxisHessian
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchCoupling
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombEstimates
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchSeparation
import Definitions.Def_OAI_Analysis_CoulombTransport_GraphBridge
import Definitions.Def_OAI_Analysis_CoulombTransport_DualCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_OptimalLocalization
import Definitions.Def_OAI_Analysis_CoulombTransport_Calibration
import Definitions.Def_OAI_Analysis_CoulombTransport_CertificateAttainment
import Definitions.Def_OAI_Analysis_CoulombTransport_SplitMeasure
import Definitions.Def_OAI_Analysis_CoulombTransport_PartitionLabel
import Definitions.Def_OAI_Analysis_CoulombTransport_CenterCertificate

open OAI OAI.Problem356 OAI.Problem356.CenterCertificate
open scoped ENNReal
open OAI OAI.Problem356 OAI.Problem356.CenterCertificate in
theorem ap_cc_norm (a b : Fin 5) : ‖point a - point b‖ = distance a b := by
  fin_cases a <;> fin_cases b <;>
    simp [point, distance, EuclideanSpace.norm_eq, Fin.sum_univ_three] <;> norm_num

open scoped ENNReal in
theorem ap_cc_lt : (5/2 : ℝ≥0∞) < 1 + 1 + (ENNReal.ofReal √2)⁻¹ := by
  have h1 : (ENNReal.ofReal √2)⁻¹ = ENNReal.ofReal (√2)⁻¹ :=
    (ENNReal.ofReal_inv_of_pos (by positivity)).symm
  have h2 : (5/2 : ℝ≥0∞) = ENNReal.ofReal (5/2) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]; norm_num
  have h3 : (1:ℝ≥0∞) + 1 + ENNReal.ofReal (√2)⁻¹ = ENNReal.ofReal (1 + 1 + (√2)⁻¹) := by
    rw [ENNReal.ofReal_add (by norm_num) (by positivity), ENNReal.ofReal_add (by norm_num) (by norm_num)]
    simp
  rw [h1, h2, h3, ENNReal.ofReal_lt_ofReal_iff (by positivity)]
  have hs : √2 < 2 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have : (2:ℝ)⁻¹ < (√2)⁻¹ := inv_strictAnti₀ (by positivity) hs
  linarith

theorem solution (i j k : Fin 5) (h : ¬ Good i j k) :
    potential i + potential j + potential k <
      coulombCost (point i, (point j, point k)) := by
  have key : ∀ a b, invDistance (point a) (point b) = (ENNReal.ofReal (distance a b))⁻¹ :=
    fun a b => by rw [invDistance, ap_cc_norm]
  simp only [coulombCost, tripleFst, tripleSnd, tripleThd, key]
  revert h
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp (config := {decide := true}) [Good, distance, potential] <;>
    first
    | exact ENNReal.div_lt_top (by norm_num) (by norm_num)
    | (convert ap_cc_lt using 1; try ring)

