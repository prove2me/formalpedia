-- Prove2me | solution 1 for LostSalesRQ.endpoint_calibrated
-- status  : ACCEPTED   (prove)
-- author  : @Ming Hu
-- created : 2026-11-17T20:53:44.004626+00:00
-- url     : https://prove2.me/submissions/bc691c71-1f19-4dc9-99cc-730567bde512

import Definitions.Def_LostSalesRQ_poisson_functions
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Intervals
import Definitions.Def_LostSalesRQ_gaussian
import Definitions.Def_LostSalesRQ_lower_curve
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.MeanInequalities
import Theorems.Thm_LostSalesRQ_intersection_penalty_formula
import Theorems.Thm_LostSalesRQ_erlang_variance_bound
import Theorems.Thm_LostSalesRQ_brownian_comparison
import Theorems.Thm_LostSalesRQ_penalty_calibration
import Theorems.Thm_LostSalesRQ_lower_curve_properties

namespace LostSalesRQ
open Finset

lemma pm_pos {μ : ℝ} (hμ : 0 < μ) (j : ℕ) : 0 < poisMass μ j := by
  unfold poisMass; positivity

lemma pm_succ (μ : ℝ) (j : ℕ) :
    poisMass μ (j + 1) * ((j : ℝ) + 1) = μ * poisMass μ j := by
  unfold poisMass
  rw [Nat.factorial_succ]
  push_cast
  have hf : (Nat.factorial j : ℝ) ≠ 0 := by positivity
  have hj : (j : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

lemma pc_succ (μ : ℝ) (j : ℕ) : poisCdf μ (j + 1) = poisCdf μ j + poisMass μ (j + 1) := by
  unfold poisCdf; rw [Finset.sum_range_succ]

lemma pc_zero (μ : ℝ) : poisCdf μ 0 = poisMass μ 0 := by simp [poisCdf]

lemma pm_le_pc {μ : ℝ} (hμ : 0 < μ) (j : ℕ) : poisMass μ j ≤ poisCdf μ j := by
  unfold poisCdf
  exact Finset.single_le_sum (fun i _ => (pm_pos hμ i).le) (Finset.self_mem_range_succ j)

lemma pc_pos {μ : ℝ} (hμ : 0 < μ) (j : ℕ) : 0 < poisCdf μ j :=
  lt_of_lt_of_le (pm_pos hμ j) (pm_le_pc hμ j)

lemma sum_i_pm (μ : ℝ) (j : ℕ) :
    ∑ i ∈ range (j + 1), (i : ℝ) * poisMass μ i = μ * (poisCdf μ j - poisMass μ j) := by
  induction j with
  | zero => simp [poisCdf]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, pc_succ]
    have h := pm_succ μ n
    push_cast
    linear_combination h

lemma sum_ii_pm (μ : ℝ) (j : ℕ) :
    ∑ i ∈ range (j + 1), (i : ℝ) * ((i : ℝ) - 1) * poisMass μ i
      = μ ^ 2 * (poisCdf μ j - poisMass μ j) - μ * (j : ℝ) * poisMass μ j := by
  induction j with
  | zero => simp [poisCdf]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, pc_succ]
    have h := pm_succ μ n
    push_cast
    linear_combination ((n : ℝ) + μ) * h

lemma lf_pos {μ : ℝ} (hμ : 0 < μ) (j : ℕ) : 0 < lossFraction μ j := by
  unfold lossFraction; exact div_pos (pm_pos hμ j) (pc_pos hμ j)

lemma lf_le_one {μ : ℝ} (hμ : 0 < μ) (j : ℕ) : lossFraction μ j ≤ 1 := by
  unfold lossFraction; rw [div_le_one (pc_pos hμ j)]; exact pm_le_pc hμ j

lemma moh_mul_pc {μ : ℝ} (hμ : 0 < μ) (j : ℕ) :
    meanOnHand μ j * poisCdf μ j = ∑ i ∈ range (j + 1), ((j : ℝ) - (i : ℝ)) * poisMass μ i := by
  have hF := pc_pos hμ j
  have h1 := sum_i_pm μ j
  have h0 : ∑ i ∈ range (j + 1), ((j : ℝ) - (i : ℝ)) * poisMass μ i
      = (j : ℝ) * poisCdf μ j - ∑ i ∈ range (j + 1), (i : ℝ) * poisMass μ i := by
    unfold poisCdf
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro i _; ring
  rw [h0, h1]
  unfold meanOnHand lossFraction
  field_simp
  ring

lemma moh_nonneg {μ : ℝ} (hμ : 0 < μ) (j : ℕ) : 0 ≤ meanOnHand μ j := by
  have hF := pc_pos hμ j
  have h := moh_mul_pc hμ j
  have hs : 0 ≤ ∑ i ∈ range (j + 1), ((j : ℝ) - (i : ℝ)) * poisMass μ i := by
    apply Finset.sum_nonneg
    intro i hi
    have hij : (i : ℝ) ≤ j := by
      have := Finset.mem_range.mp hi
      exact_mod_cast Nat.lt_succ_iff.mp this
    exact mul_nonneg (by linarith) (pm_pos hμ i).le
  by_contra hneg
  push_neg at hneg
  have : meanOnHand μ j * poisCdf μ j < 0 := mul_neg_of_neg_of_pos hneg hF
  linarith

lemma lf_succ {μ : ℝ} (hμ : 0 < μ) (j : ℕ) :
    lossFraction μ (j + 1) = μ * lossFraction μ j / (μ + meanOnHand μ j + 1) := by
  have hF := pc_pos hμ j
  have hp := pm_pos hμ j
  have h := pm_succ μ j
  have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have hHdef : meanOnHand μ j = (j : ℝ) - μ + μ * lossFraction μ j := rfl
  have hpe : poisMass μ j = lossFraction μ j * poisCdf μ j := by
    unfold lossFraction; field_simp
  have he := lf_pos hμ j
  rw [hHdef]
  set e := lossFraction μ j with he_def
  set F := poisCdf μ j with hF_def
  have hp' : poisMass μ (j + 1) = μ * e * F / ((j : ℝ) + 1) := by
    rw [eq_div_iff hj.ne', h, hpe]; ring
  show poisMass μ (j + 1) / poisCdf μ (j + 1) = _
  rw [pc_succ, hp']
  have h1 : 0 < F + μ * e * F / ((j : ℝ) + 1) := by positivity
  have h2 : 0 < μ + ((j : ℝ) - μ + μ * e) + 1 := by nlinarith
  rw [div_eq_div_iff h1.ne' h2.ne']
  field_simp
  ring

lemma ohv_eq {μ : ℝ} (hμ : 0 < μ) (j : ℕ) :
    onHandVariance μ j = μ * (1 - lossFraction μ j * (meanOnHand μ j + 1)) := by
  have hF := pc_pos hμ j
  have hFne : poisCdf μ j ≠ 0 := hF.ne'
  set H := meanOnHand μ j with hHdef
  -- reflect the sum
  have hrefl : onHandVariance μ j
      = ∑ i ∈ range (j + 1), (((j : ℝ) - (i : ℝ)) - H) ^ 2 * (poisMass μ i / poisCdf μ j) := by
    unfold onHandVariance
    rw [← Finset.sum_range_reflect]
    apply Finset.sum_congr rfl
    intro i hi
    have hij : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have h1 : j + 1 - 1 - i = j - i := by omega
    have h2 : j - (j - i) = i := by omega
    rw [h1, h2]
    push_cast [hij]
    ring
  rw [hrefl]
  have hexp : ∀ i ∈ range (j + 1), (((j : ℝ) - (i : ℝ)) - H) ^ 2 * (poisMass μ i / poisCdf μ j)
      = ((((j : ℝ) - H) ^ 2) * poisMass μ i - (2 * ((j : ℝ) - H) - 1) * ((i : ℝ) * poisMass μ i)
          + (i : ℝ) * ((i : ℝ) - 1) * poisMass μ i) / poisCdf μ j := by
    intro i _; field_simp; ring
  rw [Finset.sum_congr rfl hexp, ← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, sum_i_pm, sum_ii_pm]
  have hFdef : ∑ i ∈ range (j + 1), poisMass μ i = poisCdf μ j := rfl
  rw [hFdef]
  rw [hHdef]
  unfold meanOnHand lossFraction
  field_simp
  ring

lemma en_eq {μ : ℝ} (hμ : 0 < μ) (j : ℕ) : erlangNormalizer μ j = 1 / lossFraction μ j := by
  unfold erlangNormalizer lossFraction
  rw [one_div_div]

end LostSalesRQ

namespace LostSalesRQ

open MeasureTheory Set Real

lemma g_pdf_pos (z : ℝ) : 0 < stdNormalPdf z := by unfold stdNormalPdf; positivity

lemma g_pdf_eq (z : ℝ) : stdNormalPdf z = ProbabilityTheory.gaussianPDFReal 0 1 z := by
  unfold stdNormalPdf
  rw [ProbabilityTheory.gaussianPDFReal]
  simp only [NNReal.coe_one, mul_one, sub_zero]
  rw [div_eq_inv_mul]

lemma g_pdf_int : Integrable stdNormalPdf := by
  have : stdNormalPdf = ProbabilityTheory.gaussianPDFReal 0 1 := funext g_pdf_eq
  rw [this]; exact ProbabilityTheory.integrable_gaussianPDFReal 0 1

lemma g_pdf_integral : ∫ x, stdNormalPdf x = 1 := by
  have : stdNormalPdf = ProbabilityTheory.gaussianPDFReal 0 1 := funext g_pdf_eq
  rw [this]; exact ProbabilityTheory.integral_gaussianPDFReal_eq_one 0 one_ne_zero

lemma g_pdf_cont : Continuous stdNormalPdf := by
  unfold stdNormalPdf; fun_prop

lemma g_pdf_neg (z : ℝ) : stdNormalPdf (-z) = stdNormalPdf z := by
  unfold stdNormalPdf; rw [neg_sq]

lemma g_pdf_deriv (z : ℝ) : HasDerivAt stdNormalPdf (-z * stdNormalPdf z) z := by
  unfold stdNormalPdf
  have h1 : HasDerivAt (fun x : ℝ => -(x ^ 2) / 2) (-z) z := by
    have h := ((hasDerivAt_pow 2 z).neg).div_const 2
    have e : -((2 : ℕ) * z ^ (2 - 1)) / 2 = -z := by push_cast; ring
    rw [e] at h
    exact h
  have h2 := (h1.exp).div_const (Real.sqrt (2 * Real.pi))
  exact h2.congr_deriv (by ring)

lemma g_cdf_eq (z : ℝ) :
    stdNormalCdf z = stdNormalCdf 0 + ∫ x in (0 : ℝ)..z, stdNormalPdf x := by
  unfold stdNormalCdf
  have := intervalIntegral.integral_Iic_sub_Iic (f := stdNormalPdf) (μ := volume) (a := 0) (b := z)
    g_pdf_int.integrableOn g_pdf_int.integrableOn
  linarith

lemma g_cdf_deriv (z : ℝ) : HasDerivAt stdNormalCdf (stdNormalPdf z) z := by
  have hfun : stdNormalCdf = fun z => stdNormalCdf 0 + ∫ x in (0 : ℝ)..z, stdNormalPdf x :=
    funext g_cdf_eq
  rw [hfun]
  apply HasDerivAt.const_add
  exact intervalIntegral.integral_hasDerivAt_right (g_pdf_int.intervalIntegrable)
    (g_pdf_cont.stronglyMeasurableAtFilter _ _) g_pdf_cont.continuousAt

lemma g_cdf_tail (z : ℝ) : stdNormalCdf z + ∫ x in Ioi z, stdNormalPdf x = 1 := by
  unfold stdNormalCdf
  rw [intervalIntegral.integral_Iic_add_Ioi g_pdf_int.integrableOn g_pdf_int.integrableOn]
  exact g_pdf_integral

/-- Translation of an integral over a half line. -/
lemma g_shift (g : ℝ → ℝ) (z : ℝ) :
    ∫ x in Ioi z, g x = ∫ t in Ioi 0, g (t + z) := by
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
  rw [← integral_add_right_eq_self (μ := volume) ((Ioi z).indicator g) z]
  congr 1
  ext t
  simp only [Set.indicator, Set.mem_Ioi]
  by_cases h : 0 < t
  · rw [if_pos h, if_pos (by linarith)]
  · rw [if_neg h, if_neg (by linarith)]

/-- The Mills-type integral. -/
noncomputable def gI (z : ℝ) : ℝ := ∫ t in Ioi 0, Real.exp (z * t - t ^ 2 / 2)

lemma g_exp_int (z : ℝ) : Integrable (fun t : ℝ => Real.exp (z * t - t ^ 2 / 2)) := by
  have e : (fun t : ℝ => Real.exp (z * t - t ^ 2 / 2)) =
      fun t => Real.exp (z ^ 2 / 2) * Real.exp (-(1 / 2 : ℝ) * (t - z) ^ 2) := by
    ext t; rw [← Real.exp_add]; ring_nf
  rw [e]
  exact ((integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)).comp_sub_right z).const_mul _

lemma g_tail_rep (z : ℝ) :
    ∫ x in Ioi z, stdNormalPdf x = stdNormalPdf z * gI (-z) := by
  rw [g_shift, gI, ← integral_const_mul]
  congr 1
  ext t
  unfold stdNormalPdf
  rw [div_mul_eq_mul_div, ← Real.exp_add]
  congr 2
  ring

lemma g_cdf_rep (z : ℝ) : stdNormalCdf z = stdNormalPdf z * gI z := by
  have h1 : stdNormalCdf z = ∫ y in Ioi (-z), stdNormalPdf y := by
    unfold stdNormalCdf
    have h := integral_comp_neg_Ioi (-z) stdNormalPdf
    rw [neg_neg] at h
    rw [← h]
    congr 1
    ext y
    rw [g_pdf_neg]
  rw [h1, g_tail_rep, neg_neg, g_pdf_neg]

lemma g_I_pos (z : ℝ) : 0 < gI z := by
  unfold gI
  rw [setIntegral_pos_iff_support_of_nonneg_ae]
  · have : Function.support (fun t : ℝ => Real.exp (z * t - t ^ 2 / 2)) = univ := by
      ext t; simp [(Real.exp_pos _).ne']
    rw [this, univ_inter, Real.volume_Ioi]
    simp
  · exact Filter.Eventually.of_forall (fun t => (Real.exp_pos _).le)
  · exact (g_exp_int z).integrableOn

lemma g_cdf_pos (z : ℝ) : 0 < stdNormalCdf z := by
  rw [g_cdf_rep]; exact mul_pos (g_pdf_pos z) (g_I_pos z)

lemma g_cdf_lt_one (z : ℝ) : stdNormalCdf z < 1 := by
  have h := g_cdf_tail z
  rw [g_tail_rep] at h
  have := mul_pos (g_pdf_pos z) (g_I_pos (-z))
  linarith

end LostSalesRQ

namespace LostSalesRQ

open MeasureTheory Set Real

lemma g_moment_int {x : ℝ} (hx : 0 < x) (n : ℕ) :
    IntegrableOn (fun t : ℝ => t ^ n * Real.exp (-x * t)) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (n : ℝ)) (p := 1) (b := x)
    (by have := Nat.cast_nonneg (α := ℝ) n; linarith) one_pos hx
  refine h.congr_fun (fun t ht => ?_) measurableSet_Ioi
  simp only [Real.rpow_natCast, Real.rpow_one]

lemma g_moment {x : ℝ} (hx : 0 < x) (n : ℕ) :
    ∫ t in Ioi 0, t ^ n * Real.exp (-x * t) = (n.factorial : ℝ) / x ^ (n + 1) := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 1) (q := (n : ℝ)) (b := x) one_pos
    (by have := Nat.cast_nonneg (α := ℝ) n; linarith) hx
  have e1 : ∫ t in Ioi 0, t ^ n * Real.exp (-x * t) =
      ∫ t in Ioi 0, t ^ (n : ℝ) * Real.exp (-x * t ^ (1 : ℝ)) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    simp only [Real.rpow_natCast, Real.rpow_one]
  rw [e1, h]
  simp only [div_one, one_div, inv_one, mul_one]
  rw [Real.Gamma_nat_eq_factorial, Real.rpow_neg hx.le]
  rw [show ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  rw [div_eq_inv_mul]

lemma g_exp_quad {y : ℝ} (hy : 0 ≤ y) : Real.exp (-y) ≤ 1 - y + y ^ 2 / 2 := by
  have h4 := Real.sum_le_exp_of_nonneg hy 4
  simp [Finset.sum_range_succ, Nat.factorial] at h4
  have hpos : 0 < 1 + y + y ^ 2 / 2 + y ^ 3 / 6 := by positivity
  have hprod : Real.exp (-y) * Real.exp y = 1 := by rw [← Real.exp_add]; simp
  have hle : Real.exp (-y) * (1 + y + y ^ 2 / 2 + y ^ 3 / 6) ≤ 1 := by
    have := mul_le_mul_of_nonneg_left (by linarith : 1 + y + y ^ 2 / 2 + y ^ 3 / 6 ≤ Real.exp y)
      (Real.exp_pos (-y)).le
    linarith
  have hpoly : 1 ≤ (1 - y + y ^ 2 / 2) * (1 + y + y ^ 2 / 2 + y ^ 3 / 6) := by
    nlinarith [pow_nonneg hy 3, pow_nonneg hy 4, pow_nonneg hy 5]
  by_contra hcon
  push Not at hcon
  have := mul_lt_mul_of_pos_right hcon hpos
  linarith

end LostSalesRQ

namespace LostSalesRQ

open Finset Filter Topology

lemma cal_S0 (μ : ℝ) (j n : ℕ) (hjn : j ≤ n) :
    ∑ k ∈ Ioc j n, poisMass μ k = poisCdf μ n - poisCdf μ j := by
  induction n, hjn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [Finset.sum_Ioc_succ_top (by omega), ih, pc_succ]; ring

lemma cal_S1 (μ : ℝ) (j n : ℕ) (hjn : j ≤ n) :
    ∑ k ∈ Ioc j n, (k : ℝ) * poisMass μ k =
      μ * (poisCdf μ n - poisCdf μ j) + μ * poisMass μ j - μ * poisMass μ n := by
  induction n, hjn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [Finset.sum_Ioc_succ_top (by omega), ih, pc_succ]
    have h := pm_succ μ n
    push_cast
    linear_combination h

lemma cal_S2 (μ : ℝ) (j n : ℕ) (hjn : j ≤ n) :
    ∑ k ∈ Ioc j n, (k : ℝ) ^ 2 * poisMass μ k =
      μ ^ 2 * (poisCdf μ n - poisCdf μ j) + μ ^ 2 * poisMass μ j + μ * j * poisMass μ j
        - μ ^ 2 * poisMass μ n - μ * n * poisMass μ n
        + μ * (poisCdf μ n - poisCdf μ j) + μ * poisMass μ j - μ * poisMass μ n := by
  induction n, hjn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [Finset.sum_Ioc_succ_top (by omega), ih, pc_succ]
    have h := pm_succ μ n
    push_cast
    linear_combination ((n : ℝ) + 1 + μ) * h

lemma cal_finite_cs {μ : ℝ} (hμ : 0 < μ) (j n : ℕ) :
    (∑ k ∈ Ioc j n, (k : ℝ) * poisMass μ k) ^ 2 ≤
      (∑ k ∈ Ioc j n, poisMass μ k) * (∑ k ∈ Ioc j n, (k : ℝ) ^ 2 * poisMass μ k) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Ioc j n) (fun k : ℕ => Real.sqrt (poisMass μ k))
    (fun k : ℕ => (k : ℝ) * Real.sqrt (poisMass μ k))
  have e1 : ∀ k : ℕ, Real.sqrt (poisMass μ k) * ((k : ℝ) * Real.sqrt (poisMass μ k)) =
      (k : ℝ) * poisMass μ k := by
    intro k
    have := Real.mul_self_sqrt (pm_pos hμ k).le
    linear_combination (k : ℝ) * this
  have e2 : ∀ k : ℕ, Real.sqrt (poisMass μ k) ^ 2 = poisMass μ k := fun k =>
    Real.sq_sqrt (pm_pos hμ k).le
  have e3 : ∀ k : ℕ, ((k : ℝ) * Real.sqrt (poisMass μ k)) ^ 2 = (k : ℝ) ^ 2 * poisMass μ k := by
    intro k; rw [mul_pow, e2]
  simp only [e1, e2, e3] at h
  exact h

lemma cal_hasSum {μ : ℝ} (hμ : 0 ≤ μ) : HasSum (fun n => poisMass μ n) 1 := by
  have h := (NormedSpace.expSeries_div_hasSum_exp μ).mul_left (Real.exp (-μ))
  have e : Real.exp (-μ) * NormedSpace.exp μ = 1 := by
    rw [← Real.exp_eq_exp_ℝ, ← Real.exp_add]; simp
  rw [e] at h
  have e2 : (fun n => poisMass μ n) = fun n => Real.exp (-μ) * (μ ^ n / (n.factorial : ℝ)) := by
    funext n; unfold poisMass; ring
  rw [e2]; exact h

lemma cal_lim_F {μ : ℝ} (hμ : 0 ≤ μ) : Tendsto (fun n => poisCdf μ n) atTop (𝓝 1) := by
  have h := (cal_hasSum hμ).tendsto_sum_nat
  have h2 := h.comp (tendsto_add_atTop_nat 1)
  exact h2

lemma cal_lim_p {μ : ℝ} (hμ : 0 ≤ μ) : Tendsto (fun n => poisMass μ n) atTop (𝓝 0) :=
  (cal_hasSum hμ).summable.tendsto_atTop_zero

lemma cal_lim_np {μ : ℝ} (hμ : 0 ≤ μ) :
    Tendsto (fun n : ℕ => (n : ℝ) * poisMass μ n) atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => μ * poisMass μ n) atTop (𝓝 0) := by
    have := (cal_lim_p hμ).const_mul μ
    simpa using this
  have h2 : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * poisMass μ (n + 1)) atTop (𝓝 0) := by
    refine h.congr (fun n => ?_)
    have := pm_succ μ n
    push_cast
    linarith
  exact (tendsto_add_atTop_iff_nat 1).mp h2

/-- The upper-tail Cauchy-Schwarz inequality (nonnegative conditional variance). -/
lemma cal_tail_cs {μ : ℝ} (hμ : 0 < μ) (j : ℕ) :
    μ ^ 2 * ((1 - poisCdf μ j) + poisMass μ j) ^ 2 ≤
      (1 - poisCdf μ j) * (μ ^ 2 * ((1 - poisCdf μ j) + poisMass μ j) + μ * j * poisMass μ j +
        μ * ((1 - poisCdf μ j) + poisMass μ j)) := by
  set g : ℕ → ℝ := fun n =>
    (poisCdf μ n - poisCdf μ j) *
      (μ ^ 2 * (poisCdf μ n - poisCdf μ j) + μ ^ 2 * poisMass μ j + μ * j * poisMass μ j
        - μ ^ 2 * poisMass μ n - μ * n * poisMass μ n
        + μ * (poisCdf μ n - poisCdf μ j) + μ * poisMass μ j - μ * poisMass μ n) -
    (μ * (poisCdf μ n - poisCdf μ j) + μ * poisMass μ j - μ * poisMass μ n) ^ 2 with hg
  have hnonneg : ∀ᶠ n in atTop, 0 ≤ g n := by
    filter_upwards [eventually_ge_atTop j] with n hn
    have h := cal_finite_cs hμ j n
    rw [cal_S0 μ j n hn, cal_S1 μ j n hn, cal_S2 μ j n hn] at h
    simp only [hg]
    linarith
  have hF := (cal_lim_F hμ.le).sub_const (poisCdf μ j)
  have hp := cal_lim_p hμ.le
  have hnp := cal_lim_np hμ.le
  set G : ℝ × ℝ × ℝ → ℝ := fun x =>
    x.1 * (μ ^ 2 * x.1 + μ ^ 2 * poisMass μ j + μ * j * poisMass μ j - μ ^ 2 * x.2.1 - μ * x.2.2
      + μ * x.1 + μ * poisMass μ j - μ * x.2.1) -
    (μ * x.1 + μ * poisMass μ j - μ * x.2.1) ^ 2 with hG
  have hGc : Continuous G := by rw [hG]; fun_prop
  have hlim0 := (hGc.tendsto (1 - poisCdf μ j, 0, 0)).comp (hF.prodMk_nhds (hp.prodMk_nhds hnp))
  have hlim : Tendsto g atTop (𝓝 (G (1 - poisCdf μ j, 0, 0))) := by
    refine hlim0.congr (fun n => ?_)
    simp only [Function.comp, hG, hg]
    ring
  have := ge_of_tendsto hlim hnonneg
  simp only [hG] at this
  nlinarith [this]

end LostSalesRQ

namespace LostSalesRQ

open Finset Filter Topology

lemma cal_es_succ (t : ℝ) (l : ℕ) :
    expectedShortfall t (l + 1) = expectedShortfall t l + poisCdf t l := by
  unfold expectedShortfall poisCdf
  rw [Finset.sum_range_succ _ (l + 1)]
  push_cast
  simp only [sub_self, zero_mul, add_zero]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma cal_pt_succ (t : ℝ) (l : ℕ) : poisTail t (l + 1) = poisTail t l - poisMass t l := by
  unfold poisTail; rw [Finset.sum_range_succ]; ring

lemma cal_A_lt_succ {μ : ℝ} (hμ : 0 < μ) (l : ℕ) :
    erlangNormalizer μ l < erlangNormalizer μ (l + 1) := by
  rw [en_eq hμ, en_eq hμ]
  have h := (intersection_penalty_formula μ hμ l).2.1
  have h1 := lf_pos hμ (l + 1)
  exact one_div_lt_one_div_of_lt h1 (by linarith)

lemma cal_A_mono {μ : ℝ} (hμ : 0 < μ) : StrictMono (fun l => erlangNormalizer μ l) :=
  strictMono_nat_of_lt_succ (cal_A_lt_succ hμ)

lemma cal_F_eq {μ : ℝ} (hμ : 0 < μ) (l : ℕ) :
    poisCdf μ l = erlangNormalizer μ l * poisMass μ l := by
  unfold erlangNormalizer; field_simp [(pm_pos hμ l).ne']

/-- The rank values at weight η. -/
noncomputable def calV (μ η : ℝ) (l : ℕ) : ℝ := expectedShortfall μ l + η * poisTail μ l

lemma cal_V_succ (μ η : ℝ) (l : ℕ) :
    calV μ η (l + 1) = calV μ η l + (poisCdf μ l - η * poisMass μ l) := by
  unfold calV; rw [cal_es_succ, cal_pt_succ]; ring

lemma cal_B_eq {μ : ℝ} (hμ : 0 < μ) (j : ℕ) :
    rankBound μ (erlangNormalizer μ j) = calV μ (erlangNormalizer μ j) (j + 1) := by
  set A := erlangNormalizer μ j with hA
  have hstep : ∀ l, calV μ A (l + 1) - calV μ A l =
      poisMass μ l * (erlangNormalizer μ l - A) := by
    intro l
    rw [cal_V_succ, cal_F_eq hμ l]; ring
  have hmono := cal_A_mono hμ
  have hge : ∀ l, calV μ A (j + 1) ≤ calV μ A l := by
    intro l
    rcases le_or_gt (j + 1) l with hl | hl
    · induction l, hl using Nat.le_induction with
      | base => exact le_rfl
      | succ n hn ih =>
        have h := hstep n
        have hA' : A < erlangNormalizer μ n := hmono (by omega)
        have hp := pm_pos hμ n
        have : 0 ≤ poisMass μ n * (erlangNormalizer μ n - A) := by
          apply mul_nonneg hp.le; linarith
        linarith
    · -- l ≤ j
      have key : ∀ d l, l + d = j + 1 → calV μ A (j + 1) ≤ calV μ A l := by
        intro d
        induction d with
        | zero => intro l h; rw [show l = j + 1 by omega]
        | succ d ih =>
          intro l h
          have h1 := ih (l + 1) (by omega)
          have h := hstep l
          have hA' : erlangNormalizer μ l ≤ A := hmono.monotone (by omega)
          have hp := pm_pos hμ l
          have : poisMass μ l * (erlangNormalizer μ l - A) ≤ 0 := by
            apply mul_nonpos_of_nonneg_of_nonpos hp.le; linarith
          linarith
      exact key (j + 1 - l) l (by omega)
  unfold rankBound
  apply le_antisymm
  · exact ciInf_le ⟨calV μ A (j + 1), by rintro _ ⟨l, rfl⟩; exact hge l⟩ (j + 1)
  · exact le_ciInf (fun l => hge l)

lemma cal_V_val {μ : ℝ} (hμ : 0 < μ) (j : ℕ) :
    calV μ (erlangNormalizer μ j) (j + 1) =
      poisCdf μ j * (meanOnHand μ j + 1) + erlangNormalizer μ j * (1 - poisCdf μ j) := by
  unfold calV
  have hES : expectedShortfall μ (j + 1) = ((j : ℝ) + 1) * poisCdf μ j - μ * (poisCdf μ j - poisMass μ j) := by
    rw [cal_es_succ]
    unfold expectedShortfall
    have hs := sum_i_pm μ j
    have e : ∑ i ∈ range (j + 1), ((j : ℝ) - (i : ℝ)) * poisMass μ i =
        (j : ℝ) * poisCdf μ j - ∑ i ∈ range (j + 1), (i : ℝ) * poisMass μ i := by
      unfold poisCdf
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro i _; ring
    rw [e, hs]; ring
  have hT : poisTail μ (j + 1) = 1 - poisCdf μ j := rfl
  rw [hES, hT]
  unfold meanOnHand lossFraction
  have := pc_pos hμ j
  field_simp
  ring

lemma cal_alg (F p μ D : ℝ) (hF : 0 < F) (hp : 0 < p) (hμ : 0 < μ) :
    (F * (D + μ * (p / F)) + F / p * (1 - F)) * ((F * (D + μ * (p / F)) + F / p * (1 - F)) - D) - μ =
      ((1 - F) * (μ ^ 2 * ((1 - F) + p) + μ * (D - 1 + μ) * p + μ * ((1 - F) + p)) -
        μ ^ 2 * ((1 - F) + p) ^ 2) *
      (μ - (D + μ * (p / F)) * (D + μ * (p / F) - D)) * F ^ 2 / (μ ^ 2 * p ^ 2) := by
  field_simp
  ring

lemma cal_B_ge {μ : ℝ} (hμ : 0 < μ) (j : ℕ) (hj : 1 ≤ j) :
    ((j : ℝ) + 1 - μ + Real.sqrt (((j : ℝ) + 1 - μ) ^ 2 + 4 * μ)) / 2 ≤
      rankBound μ (erlangNormalizer μ j) := by
  rw [cal_B_eq hμ, cal_V_val hμ]
  have hF := pc_pos hμ j
  have hp := pm_pos hμ j
  have hFle1 : poisCdf μ j ≤ 1 := by
    have := (cal_hasSum hμ.le)
    have h2 := sum_le_hasSum (range (j + 1)) (fun i _ => (pm_pos hμ i).le) this
    exact h2
  have hcs := cal_tail_cs hμ j
  have hv := (erlang_variance_bound μ hμ j hj).1
  rw [ohv_eq hμ j] at hv
  set F := poisCdf μ j with hFdef
  set p := poisMass μ j with hpdef
  set D := (j : ℝ) + 1 - μ with hD
  have hA : erlangNormalizer μ j = F / p := rfl
  have hH : meanOnHand μ j + 1 = D + μ * (p / F) := by
    unfold meanOnHand lossFraction; rw [hD]; ring
  have he : lossFraction μ j = p / F := rfl
  rw [he, hH] at hv
  rw [hA, hH]
  set B := F * (D + μ * (p / F)) + F / p * (1 - F) with hB
  set E := (1 - F) * (μ ^ 2 * ((1 - F) + p) + μ * j * p + μ * ((1 - F) + p)) -
    μ ^ 2 * ((1 - F) + p) ^ 2 with hE
  have hE0 : 0 ≤ E := by rw [hE]; linarith
  have hvv : 0 ≤ μ - (D + μ * (p / F)) * (D + μ * (p / F) - D) := by
    have e : μ * (1 - p / F * (D + μ * (p / F))) = μ - (D + μ * (p / F)) * (D + μ * (p / F) - D) := by
      ring
    rw [← e]; exact hv.le
  have hjD : (j : ℝ) = D - 1 + μ := by rw [hD]; ring
  have key : B * (B - D) - μ =
      E * (μ - (D + μ * (p / F)) * (D + μ * (p / F) - D)) * F ^ 2 / (μ ^ 2 * p ^ 2) := by
    rw [hB, hE, hjD]
    clear_value B E F p D
    exact cal_alg F p μ D hF hp hμ
  have hq : 0 ≤ B * (B - D) - μ := by
    rw [key]; positivity
  have hBpos : 0 < B := by
    rw [hB]
    have : 0 ≤ F / p * (1 - F) := by
      apply mul_nonneg (div_pos hF hp).le; linarith
    have hx : 0 < D + μ * (p / F) := by
      have := moh_nonneg hμ j
      have e2 : meanOnHand μ j + 1 = D + μ * (p / F) := hH
      linarith
    have := mul_pos hF hx
    linarith
  clear_value B E
  set s := Real.sqrt (D ^ 2 + 4 * μ) with hs
  have hs2 : s ^ 2 = D ^ 2 + 4 * μ := Real.sq_sqrt (by positivity)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hsD : D < s := by
    rcases le_or_gt D 0 with h | h
    · have : 0 < s := Real.sqrt_pos.mpr (by positivity)
      linarith
    · nlinarith
  by_contra hcon
  push Not at hcon
  have h1 : B - (D + s) / 2 < 0 := by linarith
  have h2 : 0 < B - (D - s) / 2 := by linarith
  have h3 : (B - (D + s) / 2) * (B - (D - s) / 2) = B * (B - D) - μ := by
    linear_combination (-1 / 4 : ℝ) * hs2
  have h4 := mul_neg_of_neg_of_pos h1 h2
  linarith

end LostSalesRQ

namespace LostSalesRQ

open Finset Filter Topology MeasureTheory Set Real

lemma cal_log_lb {y : ℝ} (hy : 0 ≤ y) : y - y ^ 2 / 2 ≤ Real.log (1 + y) := by
  have hmono : MonotoneOn (fun y : ℝ => Real.log (1 + y) - y + y ^ 2 / 2) (Ici 0) := by
    have hd : ∀ x : ℝ, 0 ≤ x → HasDerivAt (fun y : ℝ => Real.log (1 + y) - y + y ^ 2 / 2)
        (1 / (1 + x) - 1 + x) x := by
      intro x hx
      have h1 : HasDerivAt (fun y : ℝ => 1 + y) 1 x := (hasDerivAt_id x).const_add 1
      have h2 := h1.log (by positivity)
      have h3 := (h2.sub (hasDerivAt_id x)).add ((hasDerivAt_pow 2 x).div_const 2)
      refine h3.congr_deriv ?_
      push_cast; ring_nf
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · intro x hx
      exact (hd x hx).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      exact (hd x (le_of_lt hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      have hx' : 0 < x := hx
      rw [(hd x hx'.le).deriv]
      have : 1 / (1 + x) - 1 + x = x ^ 2 / (1 + x) := by field_simp; ring
      rw [this]; positivity
  have := hmono (mem_Ici.mpr le_rfl) (mem_Ici.mpr hy) hy
  simp at this
  linarith

lemma cal_pow_lb {μ t : ℝ} (hμ : 0 < μ) (ht : 0 ≤ t) (j : ℕ) (hj : μ ≤ j) :
    Real.exp (t - t ^ 2 / (2 * μ)) ≤ (1 + t / μ) ^ j := by
  have hy : 0 ≤ t / μ := div_nonneg ht hμ.le
  have hlog := cal_log_lb hy
  have hlog0 : 0 ≤ Real.log (1 + t / μ) := Real.log_nonneg (by linarith)
  have hpos : 0 < 1 + t / μ := by linarith
  rw [← Real.exp_log (pow_pos hpos j), Real.log_pow]
  apply Real.exp_le_exp.mpr
  have e : t - t ^ 2 / (2 * μ) = μ * (t / μ - (t / μ) ^ 2 / 2) := by field_simp
  rw [e]
  have h1 : μ * (t / μ - (t / μ) ^ 2 / 2) ≤ μ * Real.log (1 + t / μ) :=
    mul_le_mul_of_nonneg_left hlog hμ.le
  have h2 : μ * Real.log (1 + t / μ) ≤ (j : ℝ) * Real.log (1 + t / μ) :=
    mul_le_mul_of_nonneg_right hj hlog0
  linarith

lemma cal_A_rep {μ : ℝ} (hμ : 0 < μ) (j : ℕ) :
    ∫ t in Ioi 0, Real.exp (-t) * (1 + t / μ) ^ j = erlangNormalizer μ j := by
  have hexp : ∀ t : ℝ, Real.exp (-t) * (1 + t / μ) ^ j =
      ∑ l ∈ range (j + 1), ((j.choose l : ℝ) / μ ^ l) * (t ^ l * Real.exp (-1 * t)) := by
    intro t
    rw [add_comm, add_pow, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    simp only [one_pow, mul_one, neg_mul, one_mul, div_pow]
    field_simp
  simp_rw [hexp]
  rw [integral_finsetSum]
  · simp_rw [integral_const_mul]
    have hm : ∀ l : ℕ, ∫ t in Ioi 0, t ^ l * Real.exp (-1 * t) = (l.factorial : ℝ) := by
      intro l
      have := g_moment (x := 1) one_pos l
      simp only [one_pow, div_one] at this
      exact this
    simp_rw [hm]
    -- A_j = ∑ C(j,l) l! / μ^l
    unfold erlangNormalizer poisCdf
    rw [Finset.sum_div]
    rw [← Finset.sum_range_reflect]
    apply Finset.sum_congr rfl
    intro l hl
    have hl' : l ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
    have e1 : j + 1 - 1 - l = j - l := by omega
    rw [e1]
    unfold poisMass
    have hc : (j.choose l : ℝ) * (l.factorial : ℝ) * ((j - l).factorial : ℝ) = (j.factorial : ℝ) := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hl'
    have hpow : μ ^ j = μ ^ (j - l) * μ ^ l := by
      rw [← pow_add]; congr 1; omega
    have h1 : (0 : ℝ) < ((j - l).factorial : ℝ) := by positivity
    have h2 : (0 : ℝ) < (l.factorial : ℝ) := by positivity
    have h3 : (0 : ℝ) < (j.factorial : ℝ) := by positivity
    have h4 := Real.exp_pos (-μ)
    rw [hpow]
    field_simp
    rw [← hc, Nat.choose_symm hl']
    ring
  · intro l _
    exact ((g_moment_int one_pos l).const_mul _)

lemma cal_A_lb {μ : ℝ} (hμ : 0 < μ) (j : ℕ) (hj : μ ≤ j) :
    Real.sqrt (Real.pi / (1 / (2 * μ))) / 2 ≤ erlangNormalizer μ j := by
  rw [← cal_A_rep hμ j]
  have hg := integral_gaussian_Ioi (1 / (2 * μ))
  rw [← hg]
  have hint1 : IntegrableOn (fun t : ℝ => Real.exp (-(1 / (2 * μ)) * t ^ 2)) (Ioi 0) :=
    (integrable_exp_neg_mul_sq (by positivity)).integrableOn
  have hint2 : IntegrableOn (fun t : ℝ => Real.exp (-t) * (1 + t / μ) ^ j) (Ioi 0) := by
    have hexp : ∀ t : ℝ, Real.exp (-t) * (1 + t / μ) ^ j =
        ∑ l ∈ range (j + 1), ((j.choose l : ℝ) / μ ^ l) * (t ^ l * Real.exp (-1 * t)) := by
      intro t
      rw [add_comm, add_pow, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      simp only [one_pow, mul_one, neg_mul, one_mul, div_pow]
      field_simp
    simp_rw [hexp]
    exact integrable_finsetSum _ (fun l _ => (g_moment_int one_pos l).const_mul _)
  apply setIntegral_mono_on hint1 hint2 measurableSet_Ioi
  intro t ht
  have ht' : (0 : ℝ) ≤ t := le_of_lt ht
  have h := cal_pow_lb hμ ht' j hj
  have e : Real.exp (-(1 / (2 * μ)) * t ^ 2) = Real.exp (-t) * Real.exp (t - t ^ 2 / (2 * μ)) := by
    rw [← Real.exp_add]; congr 1; field_simp; ring
  rw [e]
  exact mul_le_mul_of_nonneg_left h (Real.exp_pos _).le

end LostSalesRQ

namespace LostSalesRQ

open MeasureTheory Set Real

lemma cal_cdf_zero : stdNormalCdf 0 = 1 / 2 := by
  have h1 := g_cdf_tail 0
  rw [g_tail_rep, neg_zero] at h1
  have h2 := g_cdf_rep 0
  linarith

lemma cal_pdf_le (z : ℝ) : stdNormalPdf z ≤ stdNormalPdf 0 := by
  unfold stdNormalPdf
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  apply Real.exp_le_exp.mpr
  have := sq_nonneg z
  simp; nlinarith

lemma cal_pdf_quad (z : ℝ) :
    stdNormalPdf z ≤ stdNormalPdf 0 * (1 - z ^ 2 / 2 + z ^ 4 / 8) := by
  have hq := g_exp_quad (by positivity : (0 : ℝ) ≤ z ^ 2 / 2)
  have e1 : stdNormalPdf z = stdNormalPdf 0 * Real.exp (-(z ^ 2 / 2)) := by
    unfold stdNormalPdf; simp; ring_nf
  rw [e1]
  have h0 : 0 < stdNormalPdf 0 := g_pdf_pos 0
  have : (1 : ℝ) - z ^ 2 / 2 + (z ^ 2 / 2) ^ 2 / 2 = 1 - z ^ 2 / 2 + z ^ 4 / 8 := by ring
  rw [this] at hq
  exact mul_le_mul_of_nonneg_left hq h0.le

/-- Monotonicity helper on the half line. -/
lemma cal_mono_aux (g g' : ℝ → ℝ) (hd : ∀ z, HasDerivAt g (g' z) z)
    (hpos : ∀ z, 0 < z → 0 ≤ g' z) {z : ℝ} (hz : 0 ≤ z) : g 0 ≤ g z := by
  have hmono : MonotoneOn g (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · intro x _; exact (hd x).continuousAt.continuousWithinAt
    · intro x _; exact (hd x).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      rw [(hd x).deriv]
      exact hpos x hx
  exact hmono (mem_Ici.mpr le_rfl) (mem_Ici.mpr hz) hz

lemma cal_cdf_lin {z : ℝ} (hz : 0 ≤ z) : stdNormalCdf z - 1 / 2 ≤ stdNormalPdf 0 * z := by
  have h := cal_mono_aux (fun z => stdNormalPdf 0 * z - stdNormalCdf z + 1 / 2)
    (fun z => stdNormalPdf 0 - stdNormalPdf z)
    (fun z => by
      have := (((hasDerivAt_id z).const_mul (stdNormalPdf 0)).sub (g_cdf_deriv z)).add_const (1 / 2)
      refine this.congr_deriv ?_
      simp)
    (fun z _ => by have := cal_pdf_le z; linarith) hz
  simp only [mul_zero, cal_cdf_zero] at h
  linarith

lemma cal_cdf_quint {z : ℝ} (hz : 0 ≤ z) :
    stdNormalCdf z - 1 / 2 ≤ stdNormalPdf 0 * (z - z ^ 3 / 6 + z ^ 5 / 40) := by
  have h := cal_mono_aux (fun z => stdNormalPdf 0 * (z - z ^ 3 / 6 + z ^ 5 / 40) - stdNormalCdf z + 1 / 2)
    (fun z => stdNormalPdf 0 * (1 - z ^ 2 / 2 + z ^ 4 / 8) - stdNormalPdf z)
    (fun z => by
      have h1 : HasDerivAt (fun z : ℝ => z - z ^ 3 / 6 + z ^ 5 / 40) (1 - z ^ 2 / 2 + z ^ 4 / 8) z := by
        have := ((hasDerivAt_id z).sub ((hasDerivAt_pow 3 z).div_const 6)).add
          ((hasDerivAt_pow 5 z).div_const 40)
        refine this.congr_deriv ?_
        simp; ring
      have := ((h1.const_mul (stdNormalPdf 0)).sub (g_cdf_deriv z)).add_const (1 / 2)
      exact this)
    (fun z _ => by have := cal_pdf_quad z; linarith) hz
  simp only [cal_cdf_zero] at h
  norm_num at h
  linarith

lemma cal_A_part {z : ℝ} (hz : 0 ≤ z) :
    stdNormalPdf z - z * (1 - stdNormalCdf z) ≤
      stdNormalPdf 0 - z / 2 + stdNormalPdf 0 * z ^ 2 / 2 := by
  have h := cal_mono_aux
    (fun z => stdNormalPdf 0 - z / 2 + stdNormalPdf 0 * z ^ 2 / 2 - stdNormalPdf z + z * (1 - stdNormalCdf z))
    (fun z => 1 / 2 - stdNormalCdf z + stdNormalPdf 0 * z)
    (fun z => by
      have h1 := (((((hasDerivAt_const z (stdNormalPdf 0)).sub ((hasDerivAt_id z).div_const 2)).add
        (((hasDerivAt_pow 2 z).const_mul (stdNormalPdf 0)).div_const 2)).sub (g_pdf_deriv z)).add
        ((hasDerivAt_id z).mul ((hasDerivAt_const z (1 : ℝ)).sub (g_cdf_deriv z))))
      refine h1.congr_deriv ?_
      simp; ring)
    (fun z hz => by have := cal_cdf_lin hz.le; linarith) hz
  simp [cal_cdf_zero] at h
  linarith

lemma cal_w_bound {z : ℝ} (hz : 0 < z) :
    brownianProfile z ≤ stdNormalPdf 0 * (2 + z ^ 2 / 3 + z ^ 4 / 40) - z / 2 := by
  unfold brownianProfile
  rw [if_neg hz.ne']
  have hA := cal_A_part hz.le
  have hB := cal_cdf_quint hz.le
  have hB' : (stdNormalCdf z - 1 / 2) / z ≤ stdNormalPdf 0 * (1 - z ^ 2 / 6 + z ^ 4 / 40) := by
    rw [div_le_iff₀ hz]
    have e : stdNormalPdf 0 * (1 - z ^ 2 / 6 + z ^ 4 / 40) * z =
        stdNormalPdf 0 * (z - z ^ 3 / 6 + z ^ 5 / 40) := by ring
    rw [e]; exact hB
  have e2 : stdNormalPdf 0 * (2 + z ^ 2 / 3 + z ^ 4 / 40) - z / 2 =
      (stdNormalPdf 0 - z / 2 + stdNormalPdf 0 * z ^ 2 / 2) +
        stdNormalPdf 0 * (1 - z ^ 2 / 6 + z ^ 4 / 40) := by ring
  rw [e2]
  linarith

lemma cal_pdf0 : stdNormalPdf 0 = 1 / Real.sqrt (2 * Real.pi) := by
  unfold stdNormalPdf; simp

/-- The numerical comparison: sigma + w(sigma) < 2 sqrt(sqrt 2 - 1) for 0 < sigma <= sqrt(2/pi). -/
lemma cal_w_num {σ : ℝ} (hσ0 : 0 < σ) (hσ : σ ≤ 2 * stdNormalPdf 0) :
    σ + brownianProfile σ < 2 * Real.sqrt (Real.sqrt 2 - 1) := by
  have hw := cal_w_bound hσ0
  set c := 2 * stdNormalPdf 0 with hc
  have hc0 : 0 < c := by have := g_pdf_pos 0; linarith
  -- c^2 = 2/pi < 2/3.14
  have hc2 : c ^ 2 = 2 / Real.pi := by
    rw [hc, cal_pdf0, mul_pow, div_pow, one_pow, Real.sq_sqrt (by positivity)]
    field_simp
  have hpi := Real.pi_gt_d2
  have hc2' : c ^ 2 < 2 / 3.14 := by
    rw [hc2]; exact div_lt_div_of_pos_left (by norm_num) (by norm_num) hpi
  have hcub : c < 0.79809 := by nlinarith
  -- right side
  have hs2 : (1.41421 : ℝ) < Real.sqrt 2 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hr : (0.64358 : ℝ) < Real.sqrt (Real.sqrt 2 - 1) := by
    rw [Real.lt_sqrt (by norm_num)]; nlinarith
  have hσc : σ ≤ c := hσ
  -- bound sigma + w <= c (1 + sigma^2/6 + sigma^4/80) + sigma/2
  have e : stdNormalPdf 0 * (2 + σ ^ 2 / 3 + σ ^ 4 / 40) = c * (1 + σ ^ 2 / 6 + σ ^ 4 / 80) := by
    rw [hc]; ring
  rw [e] at hw
  have hσ2 : σ ^ 2 ≤ c ^ 2 := pow_le_pow_left₀ hσ0.le hσc 2
  have hσ4 : σ ^ 4 ≤ c ^ 4 := pow_le_pow_left₀ hσ0.le hσc 4
  have h1 : c * (1 + σ ^ 2 / 6 + σ ^ 4 / 80) ≤ c * (1 + c ^ 2 / 6 + c ^ 4 / 80) := by
    apply mul_le_mul_of_nonneg_left _ hc0.le; linarith
  have h2 : c * (1 + c ^ 2 / 6 + c ^ 4 / 80) + c / 2 < 1.28716 := by
    have hc3 : c ^ 3 < 0.79809 ^ 3 := pow_lt_pow_left₀ hcub hc0.le (by norm_num)
    have hc5 : c ^ 5 < 0.79809 ^ 5 := pow_lt_pow_left₀ hcub hc0.le (by norm_num)
    nlinarith
  linarith

end LostSalesRQ

namespace LostSalesRQ

open Finset Filter Topology

lemma cal_A_ge_one {μ : ℝ} (hμ : 0 < μ) (j : ℕ) : 1 ≤ erlangNormalizer μ j := by
  unfold erlangNormalizer
  rw [one_le_div (pm_pos hμ j)]
  exact pm_le_pc hμ j

lemma cal_zero_mem (μ η : ℝ) :
    (0 : ℝ) ∈ {x : ℝ | ∃ (m : ℕ) (τ : Fin m → ℝ), Monotone τ ∧ (∀ i, 0 ≤ τ i ∧ τ i ≤ μ) ∧
      x = ∑ i : Fin m, (η * poisMass (τ i) (i : ℕ) - poisCdf (τ i) (i : ℕ))} := by
  refine ⟨0, Fin.elim0, ?_, fun i => i.elim0, ?_⟩
  · intro a; exact a.elim0
  · simp

lemma cal_D_nonneg (μ η : ℝ) : 0 ≤ agingRateSup μ η := by
  unfold agingRateSup
  by_cases hb : BddAbove {x : ℝ | ∃ (m : ℕ) (τ : Fin m → ℝ), Monotone τ ∧
      (∀ i, 0 ≤ τ i ∧ τ i ≤ μ) ∧
      x = ∑ i : Fin m, (η * poisMass (τ i) (i : ℕ) - poisCdf (τ i) (i : ℕ))}
  · exact le_csSup hb (cal_zero_mem μ η)
  · rw [Real.sSup_of_not_bddAbove hb]

lemma cal_Lj {μ : ℝ} (hμ : 0 < μ) (j : ℕ) :
    baseStockCost μ (calibratedPenalty μ (erlangNormalizer μ j)) j =
      meanOnHand μ j + 1 + expectedMaxExcess μ (1 / erlangNormalizer μ j) := by
  unfold baseStockCost calibratedPenalty
  rw [en_eq hμ]
  have := (lf_pos hμ j).ne'
  field_simp
  ring

lemma cal_Ljp1_alg (μ e H W jj : ℝ) (hμ : 0 < μ) (he : 0 < e) (hH : 0 < H + 1)
    (hj : jj = H + μ - μ * e) :
    (jj + 1) - μ + μ * (μ * e / (μ + H + 1)) + (1 / e) * (1 + W) * (μ * e / (μ + H + 1)) =
      (μ * (H + 1 + W) + (H + 1) * (H + 1 + μ * (1 - e * (H + 1)) / (H + 1))) / (μ + (H + 1)) := by
  rw [hj]
  have h1 : 0 < μ + H + 1 := by linarith
  have h2 : 0 < μ + (H + 1) := by linarith
  field_simp
  ring

lemma cal_Ljp1 {μ : ℝ} (hμ : 0 < μ) (j : ℕ) :
    baseStockCost μ (calibratedPenalty μ (erlangNormalizer μ j)) (j + 1) =
      (μ * (meanOnHand μ j + 1 + expectedMaxExcess μ (1 / erlangNormalizer μ j)) +
        (meanOnHand μ j + 1) * (meanOnHand μ j + 1 + onHandVariance μ j / (meanOnHand μ j + 1))) /
        (μ + (meanOnHand μ j + 1)) := by
  have hH := moh_nonneg hμ j
  have he := lf_pos hμ j
  have hv := ohv_eq hμ j
  have hs := lf_succ hμ j
  have hHdef : meanOnHand μ (j + 1) = ((j + 1 : ℕ) : ℝ) - μ + μ * lossFraction μ (j + 1) := rfl
  have hHj : meanOnHand μ j = (j : ℝ) - μ + μ * lossFraction μ j := rfl
  unfold baseStockCost calibratedPenalty
  rw [hHdef, hs, hv, en_eq hμ j]
  push_cast
  have hjj : (j : ℝ) = meanOnHand μ j + μ - μ * lossFraction μ j := by rw [hHj]; ring
  rw [hjj]
  have hW : expectedMaxExcess μ (1 / (1 / lossFraction μ j)) =
      expectedMaxExcess μ (1 / erlangNormalizer μ j) := by rw [en_eq hμ j]
  rw [hW]
  generalize expectedMaxExcess μ (1 / erlangNormalizer μ j) = W
  generalize lossFraction μ j = e at he ⊢
  generalize meanOnHand μ j = H at hH ⊢
  exact cal_Ljp1_alg μ e H W (H + μ - μ * e) hμ he (by linarith) rfl

lemma cal_quad {β D μ : ℝ} (hμ : 0 < μ) (hD : 0 ≤ D)
    (hβ : β = (D + Real.sqrt (D ^ 2 + 4 * μ)) / 2) :
    0 < β ∧ D ≤ β ∧ β ^ 2 = D * β + μ := by
  have hs0 := Real.sqrt_nonneg (D ^ 2 + 4 * μ)
  have hs2 := Real.sq_sqrt (show (0 : ℝ) ≤ D ^ 2 + 4 * μ by positivity)
  have hsD : D ≤ Real.sqrt (D ^ 2 + 4 * μ) := by
    rw [Real.le_sqrt hD (by positivity)]; linarith
  have hspos : 0 < Real.sqrt (D ^ 2 + 4 * μ) := Real.sqrt_pos.mpr (by positivity)
  refine ⟨by rw [hβ]; linarith, by rw [hβ]; linarith, ?_⟩
  rw [hβ]
  nlinarith [hs2]

lemma cal_Lja {μ : ℝ} (hμ : 0 < μ) (j : ℕ) (hj : 1 ≤ j) (hjμ : μ ≤ j) (β : ℝ)
    (hβ : β = (((j : ℝ) + 1 - μ) + Real.sqrt (((j : ℝ) + 1 - μ) ^ 2 + 4 * μ)) / 2) :
    meanOnHand μ j + 1 + onHandVariance μ j / (meanOnHand μ j + 1) < Real.sqrt 2 * β := by
  obtain ⟨_, _, _, _, hL5, hL6⟩ := intersection_penalty_formula μ hμ j
  have hA3 := (erlang_variance_bound μ hμ j hj).2
  have hH := moh_nonneg hμ j
  have hv := ohv_eq hμ j
  set D := (j : ℝ) + 1 - μ with hD
  have hD1 : 1 ≤ D := by rw [hD]; linarith
  obtain ⟨hβ0, hDβ, hβ2⟩ := cal_quad hμ (by linarith) hβ
  set x := meanOnHand μ j + 1 with hx
  have hx0 : 0 < x := by linarith
  have he : μ * lossFraction μ j = x - D := by
    rw [hx, hD]; unfold meanOnHand; ring
  have hvv : onHandVariance μ j = μ - x * (x - D) := by
    rw [hv, ← he]; ring
  have hL : x + onHandVariance μ j / x = D + μ / x := by
    rw [hvv]; field_simp; ring
  rw [hL]
  have hmu : μ ≤ x * (2 * x - 1 - D) := by
    rw [hvv] at hA3
    have : meanOnHand μ j = x - 1 := by rw [hx]; ring
    rw [this] at hA3
    nlinarith
  set L := D + μ / x with hLdef
  have hLD : D ≤ L := by have : 0 < μ / x := by positivity
                         linarith
  have hLL : L * (L - D) < 2 * μ := by
    have e : L * (L - D) = μ * (D / x + μ / x ^ 2) := by rw [hLdef]; field_simp; ring
    rw [e]
    have h1 : μ / x ^ 2 ≤ (2 * x - 1 - D) / x := by
      rw [div_le_div_iff₀ (by positivity) hx0]; nlinarith
    have h2 : D / x + μ / x ^ 2 < 2 := by
      have : D / x + (2 * x - 1 - D) / x = 2 - 1 / x := by field_simp; ring
      have : 0 < 1 / x := by positivity
      linarith
    nlinarith
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs1 : 1 < Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hs22 : Real.sqrt 2 < 2 := by nlinarith
  have hbig : 2 * μ ≤ Real.sqrt 2 * β * (Real.sqrt 2 * β - D) := by
    have e : Real.sqrt 2 * β * (Real.sqrt 2 * β - D) = 2 * μ + (2 - Real.sqrt 2) * D * β := by
      have : Real.sqrt 2 * β * (Real.sqrt 2 * β - D) = Real.sqrt 2 ^ 2 * β ^ 2 - Real.sqrt 2 * D * β := by ring
      rw [this, hs2, hβ2]; ring
    rw [e]
    have : 0 ≤ (2 - Real.sqrt 2) * D * β := by
      apply mul_nonneg (mul_nonneg (by linarith) (by linarith)) hβ0.le
    linarith
  by_contra hcon
  push Not at hcon
  have hb2 : D ≤ Real.sqrt 2 * β := by
    have := mul_le_mul_of_nonneg_right hs1.le hβ0.le
    linarith
  have hm := mul_le_mul hcon (by linarith : Real.sqrt 2 * β - D ≤ L - D) (by linarith) (by linarith)
  linarith

lemma cal_Lj_bound {μ : ℝ} (hμ : 0 < μ) (j : ℕ) (hjμ : μ ≤ j) (β : ℝ)
    (hβ : β = (((j : ℝ) + 1 - μ) + Real.sqrt (((j : ℝ) + 1 - μ) ^ 2 + 4 * μ)) / 2) :
    meanOnHand μ j + 1 + expectedMaxExcess μ (1 / erlangNormalizer μ j) < Real.sqrt 2 * β := by
  set A := erlangNormalizer μ j with hAdef
  have hA1 := cal_A_ge_one hμ j
  have hA0 : 0 < A := by linarith
  set D := (j : ℝ) + 1 - μ with hD
  have hD1 : 1 ≤ D := by rw [hD]; linarith
  obtain ⟨hβ0, hDβ, hβ2⟩ := cal_quad hμ (by linarith) hβ
  set r := Real.sqrt μ with hr
  have hr0 : 0 < r := Real.sqrt_pos.mpr hμ
  have hr2 : r ^ 2 = μ := Real.sq_sqrt hμ.le
  set σ := (1 / A) * r with hσ
  have hσ0 : 0 < σ := by positivity
  -- sigma <= 2 phi(0)
  have hAlb := cal_A_lb hμ j hjμ
  have hσc : σ ≤ 2 * stdNormalPdf 0 := by
    rw [cal_pdf0]
    have e1 : Real.sqrt (Real.pi / (1 / (2 * μ))) = Real.sqrt (2 * Real.pi) * r := by
      rw [hr, ← Real.sqrt_mul (by positivity)]; congr 1; field_simp
    rw [e1] at hAlb
    have hsp : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
    rw [hσ]
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hA0]
    have : 2 * (1 / Real.sqrt (2 * Real.pi)) * A ≥ 2 * (1 / Real.sqrt (2 * Real.pi)) *
        (Real.sqrt (2 * Real.pi) * r / 2) := by
      apply mul_le_mul_of_nonneg_left hAlb; positivity
    have e2 : 2 * (1 / Real.sqrt (2 * Real.pi)) * (Real.sqrt (2 * Real.pi) * r / 2) = r := by
      field_simp
    linarith
  -- Brownian comparison
  have hW := brownian_comparison μ (1 / A) hμ (by positivity) (by rw [div_le_one hA0]; exact hA1)
  rw [← hσ] at hW
  have hwnum := cal_w_num hσ0 hσc
  -- x = D + r sigma
  have hx : meanOnHand μ j + 1 = D + r * σ := by
    have he : lossFraction μ j = 1 / A := by rw [hAdef, en_eq hμ]; field_simp
    unfold meanOnHand
    rw [he, hσ, hD]
    have : μ = r * r := by rw [← sq, hr2]
    rw [this]; ring
  rw [hx]
  -- AM-GM
  set K := 2 * Real.sqrt (Real.sqrt 2 - 1) with hK
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs1 : 1 < Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hK2 : K ^ 2 = 4 * (Real.sqrt 2 - 1) := by
    rw [hK, mul_pow, Real.sq_sqrt (by linarith)]; ring
  have hK0 : 0 ≤ K := by positivity
  have hamgm : K * r ≤ Real.sqrt 2 * β - D := by
    have e : Real.sqrt 2 * β - D = (Real.sqrt 2 - 1) * β + μ / β := by
      field_simp
      nlinarith [hβ2]
    rw [e]
    set a := (Real.sqrt 2 - 1) * β
    set b := μ / β
    have ha : 0 ≤ a := mul_nonneg (by linarith) hβ0.le
    have hb : 0 ≤ b := by positivity
    have hab : a * b = (Real.sqrt 2 - 1) * μ := by
      simp only [a, b]; field_simp
    have hsq : (K * r) ^ 2 ≤ (a + b) ^ 2 := by
      rw [mul_pow, hK2, hr2]
      nlinarith [sq_nonneg (a - b)]
    nlinarith [sq_nonneg (K * r - (a + b)), mul_nonneg hK0 hr0.le]
  have h1 := mul_lt_mul_of_pos_left hwnum hr0
  have e3 : r * (σ + brownianProfile σ) = r * σ + r * brownianProfile σ := by ring
  have e4 : r * K = K * r := by ring
  rw [e3, e4] at h1
  linarith

end LostSalesRQ

open LostSalesRQ in
theorem solution (μ : ℝ) (hμ : 0 < μ) :
    (∀ j : ℕ, μ ≤ (j : ℝ) →
      max (baseStockCost μ (calibratedPenalty μ (erlangNormalizer μ j)) j)
          (baseStockCost μ (calibratedPenalty μ (erlangNormalizer μ j)) (j + 1)) <
        Real.sqrt 2 * rankBound μ (erlangNormalizer μ j) ∧
      Real.sqrt 2 * rankBound μ (erlangNormalizer μ j) ≤
        Real.sqrt 2 * lowerCurve μ (calibratedPenalty μ (erlangNormalizer μ j))) ∧
    StrictMonoOn (fun j : ℕ => calibratedPenalty μ (erlangNormalizer μ j))
      {j : ℕ | μ ≤ (j : ℝ)} ∧
    Filter.Tendsto (fun j : ℕ => calibratedPenalty μ (erlangNormalizer μ j))
      Filter.atTop Filter.atTop := by
  have hs0 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · intro j hjμ
    have hj1 : 1 ≤ j := by
      have : (0 : ℝ) < j := lt_of_lt_of_le hμ hjμ
      have : 0 < j := by exact_mod_cast this
      omega
    set β := ((j : ℝ) + 1 - μ + Real.sqrt (((j : ℝ) + 1 - μ) ^ 2 + 4 * μ)) / 2 with hβ
    have hB := cal_B_ge hμ j hj1
    have h1 := cal_Lj_bound hμ j hjμ β hβ
    have h2 := cal_Lja hμ j hj1 hjμ β hβ
    have hH := moh_nonneg hμ j
    refine ⟨?_, ?_⟩
    · have hx : 0 < meanOnHand μ j + 1 := by linarith
      have hL1 : baseStockCost μ (calibratedPenalty μ (erlangNormalizer μ j)) j < Real.sqrt 2 * β := by
        rw [cal_Lj hμ j]; exact h1
      have hL2 : baseStockCost μ (calibratedPenalty μ (erlangNormalizer μ j)) (j + 1) <
          Real.sqrt 2 * β := by
        rw [cal_Ljp1 hμ j, div_lt_iff₀ (by linarith)]
        have i1 := mul_lt_mul_of_pos_left h1 hμ
        have i2 := mul_lt_mul_of_pos_left h2 hx
        nlinarith
      have hβB : Real.sqrt 2 * β ≤ Real.sqrt 2 * rankBound μ (erlangNormalizer μ j) :=
        mul_le_mul_of_nonneg_left hB hs0.le
      exact max_lt (lt_of_lt_of_le hL1 hβB) (lt_of_lt_of_le hL2 hβB)
    · exact mul_le_mul_of_nonneg_left
        ((lower_curve_properties μ hμ.le).2.1 _ (cal_A_ge_one hμ j)) hs0.le
  · intro i _ k _ hik
    exact (penalty_calibration μ hμ.le).2.2.1 (Set.mem_Ici.mpr (cal_A_ge_one hμ i))
      (Set.mem_Ici.mpr (cal_A_ge_one hμ k)) (cal_A_mono hμ hik)
  · rw [Filter.tendsto_atTop_atTop]
    intro b
    refine ⟨max 1 ⌈b + μ⌉₊, fun j hj => ?_⟩
    have hj1 : 1 ≤ j := le_trans (le_max_left _ _) hj
    have hjb : b + μ ≤ (j : ℝ) := by
      have h1 := Nat.le_ceil (b + μ)
      have h2 : (⌈b + μ⌉₊ : ℝ) ≤ j := by exact_mod_cast le_trans (le_max_right _ _) hj
      linarith
    have hcal := (penalty_calibration μ hμ.le).1 _ (cal_A_ge_one hμ j)
    have hD := cal_D_nonneg μ (erlangNormalizer μ j)
    have hB := cal_B_ge hμ j hj1
    have hsq : (j : ℝ) + 1 - μ ≤ Real.sqrt (((j : ℝ) + 1 - μ) ^ 2 + 4 * μ) := by
      rcases le_or_gt ((j : ℝ) + 1 - μ) 0 with h | h
      · exact le_trans h (Real.sqrt_nonneg _)
      · rw [Real.le_sqrt h.le (by positivity)]; nlinarith
    show b ≤ calibratedPenalty μ (erlangNormalizer μ j)
    linarith
