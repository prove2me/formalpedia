-- Prove2me | solution 1 for OAI.Problem356.FiveComponentGeometry.strict_center_gap
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T22:32:26.156505+00:00
-- url     : https://prove2.me/submissions/a1cef5eb-a683-4292-84bd-b952abddd76a

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
import Definitions.Def_OAI_Analysis_CoulombTransport_CommonBranches
import Definitions.Def_OAI_Analysis_CoulombTransport_DensityMeasure
import Definitions.Def_OAI_Analysis_CoulombTransport_ComponentPotential
import Definitions.Def_OAI_Analysis_CoulombTransport_LocalImplicit
import Definitions.Def_OAI_Analysis_CoulombTransport_HessianCLM
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombCalculus
import Definitions.Def_OAI_Analysis_CoulombTransport_StationaryEquation
import Definitions.Def_OAI_Analysis_CoulombTransport_HessianMatrix
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombCoercivity
import Definitions.Def_OAI_Analysis_CoulombTransport_LocalCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_StationaryMap
import Definitions.Def_OAI_Analysis_CoulombTransport_LocalBranchMeasure
import Definitions.Def_OAI_Analysis_CoulombTransport_SmoothPushforward
import Definitions.Def_OAI_Analysis_CoulombTransport_GluedCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_GoodTypePermutation
import Definitions.Def_OAI_Analysis_CoulombTransport_IsometryTransport
import Definitions.Def_OAI_Analysis_CoulombTransport_SmoothBranchMarginal
import Definitions.Def_OAI_Analysis_CoulombTransport_StateDual
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombSupportExistence
import Definitions.Def_OAI_Analysis_CoulombTransport_FiveComponentGeometry

open OAI OAI.Problem356 OAI.Problem356.FiveComponentGeometry
open Set Filter Metric
open scoped ENNReal InnerProductSpace
open LocalGeometry StationaryMap CenterCertificate
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

open OAI OAI.Problem356 OAI.Problem356.CenterCertificate in
open scoped ENNReal in
theorem h41_son (i j k : Fin 5) (h : ¬ Good i j k) :
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

open OAI OAI.Problem356 StationaryMap in
theorem h41_val (a : E3) (ha : ‖a‖ = 1) : jointPotential a (a, (0, -a)) = 0 := by
  have h2 : ‖-a - a‖ = 2 := by
    rw [show -a - a = -((2:ℝ) • a) by rw [two_smul]; abel, norm_neg, norm_smul, ha]; norm_num
  simp only [jointPotential, statePotential, CoulombCalculus.pairCost, zero_sub, norm_neg, ha,
    sub_neg_eq_add, zero_add, h2, neg_add_cancel, inner_zero_right, norm_zero]
  norm_num

open OAI OAI.Problem356 CenterCertificate in
theorem h41_p1 : ‖point 1‖ = 1 := by
  simp [point, EuclideanSpace.norm_eq, Fin.sum_univ_three]

open OAI OAI.Problem356 CenterCertificate in
theorem h41_p3 : ‖point 3‖ = 1 := by
  simp [point, EuclideanSpace.norm_eq, Fin.sum_univ_three]

open OAI OAI.Problem356 CenterCertificate in
theorem h41_p2 : point 2 + point 1 = 0 := by
  ext i; fin_cases i <;> simp [point]

open OAI OAI.Problem356 CenterCertificate in
theorem h41_p4 : point 4 + point 3 = 0 := by
  ext i; fin_cases i <;> simp [point]

open OAI OAI.Problem356 CenterCertificate in
theorem h41_p0 : point 0 = 0 := by
  ext i; fin_cases i <;> simp [point]

theorem solution (C₁ : ChartsAt (point 1)) (C₂ : ChartsAt (point 3))
    (i j k : Fin 5) (h : ¬ Good i j k) :
    ENNReal.ofReal (potentials C₁ C₂ i (point i) +
      potentials C₁ C₂ j (point j) + potentials C₁ C₂ k (point k)) <
      coulombCost (point i, (point j, point k)) := by
  have q0 : potentials C₁ C₂ 0 (point 0) = 5 / 2 := by
    show (5 : ℝ) / 2 - 10 * ‖point 0‖ ^ 2 = 5 / 2
    simp [h41_p0]
  have q1 : potentials C₁ C₂ 1 (point 1) = 0 := by
    show C₁.value (point 1) = 0
    rw [C₁.value_base]; exact h41_val _ h41_p1
  have q2 : potentials C₁ C₂ 2 (point 2) = 0 := by
    show (5 : ℝ) / 4 * inner ℝ (point 1) (point 2 + point 1) - 10 * ‖point 2 + point 1‖ ^ 2 = 0
    simp [h41_p2]
  have q3 : potentials C₁ C₂ 3 (point 3) = 0 := by
    show C₂.value (point 3) = 0
    rw [C₂.value_base]; exact h41_val _ h41_p3
  have q4 : potentials C₁ C₂ 4 (point 4) = 0 := by
    show (5 : ℝ) / 4 * inner ℝ (point 3) (point 4 + point 3) - 10 * ‖point 4 + point 3‖ ^ 2 = 0
    simp [h41_p4]
  have hpot : ∀ i, potentials C₁ C₂ i (point i) = (potential i).toReal := by
    intro i
    fin_cases i
    · rw [show ((⟨0, by decide⟩ : Fin 5)) = 0 from rfl, q0]; simp [potential]
    · rw [show ((⟨1, by decide⟩ : Fin 5)) = 1 from rfl, q1]; simp [potential]
    · rw [show ((⟨2, by decide⟩ : Fin 5)) = 2 from rfl, q2]; simp [potential]
    · rw [show ((⟨3, by decide⟩ : Fin 5)) = 3 from rfl, q3]; simp [potential]
    · rw [show ((⟨4, by decide⟩ : Fin 5)) = 4 from rfl, q4]; simp [potential]
  have hne : ∀ i, potential i ≠ ⊤ := by
    intro i; unfold potential; split_ifs <;> simp [ENNReal.div_eq_top]
  have hsum : ENNReal.ofReal (potentials C₁ C₂ i (point i) +
      potentials C₁ C₂ j (point j) + potentials C₁ C₂ k (point k)) =
      potential i + potential j + potential k := by
    rw [hpot, hpot, hpot, ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_toReal (hne i),
      ENNReal.ofReal_toReal (hne j), ENNReal.ofReal_toReal (hne k)]
  rw [hsum]
  exact h41_son i j k h

