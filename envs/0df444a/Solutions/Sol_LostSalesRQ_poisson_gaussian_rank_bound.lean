-- Prove2me | solution 1 for LostSalesRQ.poisson_gaussian_rank_bound
-- status  : ACCEPTED   (prove)
-- author  : @Ming Hu
-- created : 2026-11-17T21:51:02.356623+00:00
-- url     : https://prove2.me/submissions/4d238411-873a-4f21-b280-ec05ea267628

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
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

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

open MeasureTheory Set Real Filter Topology

lemma g_I_neg_eq (x : ℝ) : gI (-x) = ∫ t in Ioi 0, Real.exp (-x * t) * Real.exp (-(t ^ 2) / 2) := by
  unfold gI
  congr 1; ext t
  rw [← Real.exp_add]; ring_nf

lemma g_I_neg_lt {x : ℝ} (hx : 0 < x) : gI (-x) < 1 / x := by
  have h1 : ∫ t in Ioi 0, Real.exp (-x * t) = 1 / x := by
    rw [integral_exp_mul_Ioi (by linarith : -x < 0) 0]; simp
  have hint1 : IntegrableOn (fun t : ℝ => Real.exp (-x * t)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi (by linarith) 0
  have hint2 : IntegrableOn (fun t : ℝ => Real.exp (-x * t) * Real.exp (-(t ^ 2) / 2)) (Ioi 0) := by
    have := (g_exp_int (-x)).integrableOn (s := Ioi 0)
    refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
    rw [← Real.exp_add]; ring_nf
  have hpos : 0 < ∫ t in Ioi 0, (Real.exp (-x * t) - Real.exp (-x * t) * Real.exp (-(t ^ 2) / 2)) := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae]
    · have hsub : Ioi (0 : ℝ) ⊆ Function.support
          (fun t : ℝ => Real.exp (-x * t) - Real.exp (-x * t) * Real.exp (-(t ^ 2) / 2)) ∩ Ioi 0 := by
        intro t ht
        refine ⟨?_, ht⟩
        have ht' : (0 : ℝ) < t := ht
        have hlt : Real.exp (-(t ^ 2) / 2) < 1 := by
          rw [Real.exp_lt_one_iff]; nlinarith
        have he := Real.exp_pos (-x * t)
        simp only [Function.mem_support]
        nlinarith
      have := measure_mono (μ := volume) hsub
      rw [Real.volume_Ioi] at this
      exact lt_of_lt_of_le (by simp) this
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall (fun t ht => ?_))
      have hle : Real.exp (-(t ^ 2) / 2) ≤ 1 := by rw [Real.exp_le_one_iff]; nlinarith
      have he := Real.exp_pos (-x * t)
      simp only [Pi.zero_apply]
      nlinarith
    · exact hint1.sub hint2
  rw [integral_sub hint1 hint2, h1, ← g_I_neg_eq] at hpos
  linarith

noncomputable def gU (z : ℝ) : ℝ := stdNormalCdf z / stdNormalPdf z

lemma gU_eq (z : ℝ) : gU z = gI z := by
  unfold gU; rw [g_cdf_rep]; field_simp [(g_pdf_pos z).ne']

lemma gU_pos (z : ℝ) : 0 < gU z := by rw [gU_eq]; exact g_I_pos z

lemma g_one_add (z : ℝ) : 0 < 1 + z * gU z := by
  rcases le_or_gt 0 z with hz | hz
  · have := gU_pos z; nlinarith
  · have hx : 0 < -z := by linarith
    have h := g_I_neg_lt hx
    rw [neg_neg] at h
    rw [gU_eq]
    have : (-z) * gI z < 1 := by
      have := mul_lt_mul_of_pos_left h hx
      rw [mul_one_div_cancel hx.ne'] at this
      exact this
    linarith

lemma g2_crossing (f : ℝ → ℝ) (a : ℝ)
    (hd : ∀ t, a ≤ t → ∃ d, HasDerivAt f d t ∧ (f t = 0 → d < 0))
    (hlarge : ∀ M, ∃ t, M ≤ t ∧ 0 < f t) : ∀ t, a ≤ t → 0 < f t := by
  intro t0 ht0
  by_contra hneg
  push Not at hneg
  obtain ⟨t1, ht1, hf1⟩ := hlarge (t0 + 1)
  have hcont : ∀ t, a ≤ t → ContinuousAt f t := fun t ht => by
    obtain ⟨d, hdt, _⟩ := hd t ht; exact hdt.continuousAt
  have hcontOn : ContinuousOn f (Set.Icc t0 t1) := fun t ht =>
    (hcont t (le_trans ht0 ht.1)).continuousWithinAt
  set S := Set.Icc t0 t1 ∩ f ⁻¹' Set.Iic 0 with hS
  have hSc : IsClosed S := hcontOn.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hSne : S.Nonempty := ⟨t0, ⟨le_refl _, by linarith⟩, hneg⟩
  have hSb : BddAbove S := ⟨t1, fun t ht => ht.1.2⟩
  have hsS : sSup S ∈ S := hSc.csSup_mem hSne hSb
  set s := sSup S with hsdef
  have hfs : f s ≤ 0 := hsS.2
  have hst1 : s < t1 := by
    rcases lt_or_eq_of_le hsS.1.2 with h | h
    · exact h
    · exfalso; rw [h] at hfs; linarith
  have hpos : ∀ t, s < t → t ≤ t1 → 0 < f t := by
    intro t hst htt1
    by_contra hc
    push Not at hc
    have hmem : t ∈ S := ⟨⟨by linarith [hsS.1.1], htt1⟩, hc⟩
    have := le_csSup hSb hmem
    linarith
  have has : a ≤ s := le_trans ht0 hsS.1.1
  have hfs0 : f s = 0 := by
    by_contra hne
    have hlt : f s < 0 := lt_of_le_of_ne hfs hne
    have hev : ∀ᶠ y in 𝓝 s, f y < 0 := (hcont s has).eventually (Iio_mem_nhds hlt)
    have hev2 : ∀ᶠ y in 𝓝[>] s, f y < 0 ∧ y ∈ Set.Ioo s t1 :=
      (hev.filter_mono nhdsWithin_le_nhds).and (Ioo_mem_nhdsGT hst1)
    obtain ⟨y, hy1, hy2⟩ := hev2.exists
    linarith [hpos y hy2.1 hy2.2.le]
  obtain ⟨d, hdd, hdneg⟩ := hd s has
  have hd0 := hdneg hfs0
  have hslope := hasDerivAt_iff_tendsto_slope.mp hdd
  have hev : ∀ᶠ y in 𝓝[≠] s, slope f s y < 0 := hslope.eventually (Iio_mem_nhds hd0)
  have hev' : ∀ᶠ y in 𝓝[>] s, slope f s y < 0 :=
    hev.filter_mono (nhdsWithin_mono s fun y hy => Set.mem_compl_singleton_iff.mpr (ne_of_gt hy))
  obtain ⟨y, hy1, hy2⟩ := (hev'.and (Ioo_mem_nhdsGT hst1)).exists
  rw [slope_def_field, hfs0] at hy1
  have hys : 0 < y - s := by linarith [hy2.1]
  have hfy : f y - 0 < 0 := by
    by_contra hc
    push Not at hc
    have := div_nonneg hc hys.le
    linarith
  linarith [hpos y hy2.1 hy2.2.le]

lemma g_tail_eq (z : ℝ) : 1 - stdNormalCdf z = stdNormalPdf z * gI (-z) := by
  have h := g_cdf_tail z
  rw [g_tail_rep] at h
  linarith

end LostSalesRQ

namespace LostSalesRQ

open MeasureTheory Set Real Filter Topology

lemma q_cdf_cont : Continuous stdNormalCdf :=
  continuous_iff_continuousAt.mpr (fun z => (g_cdf_deriv z).continuousAt)

lemma q_cdf_strictMono : StrictMono stdNormalCdf :=
  strictMono_of_deriv_pos (fun x => by rw [(g_cdf_deriv x).deriv]; exact g_pdf_pos x)

lemma q_pdf_le_one (z : ℝ) : stdNormalPdf z ≤ 1 := by
  unfold stdNormalPdf
  have h1 : Real.exp (-(z ^ 2) / 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith [sq_nonneg z]
  have h2 : 1 ≤ Real.sqrt (2 * Real.pi) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]; nlinarith [Real.pi_gt_three]
  rw [div_le_one (by linarith)]
  linarith

lemma q_cdf_neg_le {x : ℝ} (hx : 0 < x) : stdNormalCdf (-x) ≤ 1 / x := by
  rw [g_cdf_rep, g_pdf_neg]
  have h1 := g_I_neg_lt hx
  have h2 := q_pdf_le_one x
  have h3 := g_pdf_pos x
  have h4 := g_I_pos (-x)
  calc stdNormalPdf x * gI (-x) ≤ 1 * gI (-x) := mul_le_mul_of_nonneg_right h2 h4.le
    _ ≤ 1 / x := by linarith

lemma q_cdf_ge {x : ℝ} (hx : 0 < x) : 1 - 1 / x ≤ stdNormalCdf x := by
  have h := g_tail_eq x
  have h1 := g_I_neg_lt hx
  have h2 := q_pdf_le_one x
  have h4 := g_I_pos (-x)
  have : stdNormalPdf x * gI (-x) ≤ 1 / x := by
    calc stdNormalPdf x * gI (-x) ≤ 1 * gI (-x) := mul_le_mul_of_nonneg_right h2 h4.le
      _ ≤ 1 / x := by linarith
  linarith

lemma q_tendsto_top : Tendsto stdNormalCdf atTop (𝓝 1) := by
  have hlow : Tendsto (fun x : ℝ => 1 - 1 / x) atTop (𝓝 1) := by
    have h : Tendsto (fun x : ℝ => 1 / x) atTop (𝓝 0) := by
      simpa [one_div] using tendsto_inv_atTop_zero
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with x hx
    exact q_cdf_ge hx
  · exact Eventually.of_forall (fun x => (g_cdf_lt_one x).le)

lemma q_tendsto_bot : Tendsto stdNormalCdf atBot (𝓝 0) := by
  have hup : Tendsto (fun z : ℝ => 1 / (-z)) atBot (𝓝 0) := by
    have h := (tendsto_inv_atTop_zero (𝕜 := ℝ)).comp (tendsto_neg_atBot_atTop (G := ℝ))
    refine h.congr (fun z => ?_)
    simp [one_div]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · exact Eventually.of_forall (fun z => (g_cdf_pos z).le)
  · filter_upwards [eventually_lt_atBot 0] with z hz
    have := q_cdf_neg_le (x := -z) (by linarith)
    rwa [neg_neg] at this

lemma q_surj {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) : ∃ z, stdNormalCdf z = u := by
  set m := min u (1 - u) with hm
  have hm0 : 0 < m := lt_min hu0 (by linarith)
  have hmu : m ≤ u := min_le_left _ _
  have hmu' : m ≤ 1 - u := min_le_right _ _
  have hx : 0 < 2 / m := by positivity
  have h1 : stdNormalCdf (-(2 / m)) < u := by
    have := q_cdf_neg_le hx
    have e : 1 / (2 / m) = m / 2 := by field_simp
    rw [e] at this
    linarith
  have h2 : u < stdNormalCdf (2 / m) := by
    have := q_cdf_ge hx
    have e : 1 / (2 / m) = m / 2 := by field_simp
    rw [e] at this
    linarith
  obtain ⟨z, _, hz⟩ := intermediate_value_Icc (by linarith : -(2 / m) ≤ 2 / m)
    q_cdf_cont.continuousOn ⟨h1.le, h2.le⟩
  exact ⟨z, hz⟩

/-- The normal distribution function as a map into the open unit interval. -/
noncomputable def qF (z : ℝ) : Set.Ioo (0 : ℝ) 1 := ⟨stdNormalCdf z, g_cdf_pos z, g_cdf_lt_one z⟩

lemma qF_strictMono : StrictMono qF := fun a b hab => by
  show stdNormalCdf a < stdNormalCdf b
  exact q_cdf_strictMono hab

lemma qF_surj : Function.Surjective qF := by
  rintro ⟨u, hu⟩
  obtain ⟨z, hz⟩ := q_surj hu.1 hu.2
  exact ⟨z, Subtype.ext hz⟩

noncomputable def qIso : ℝ ≃o Set.Ioo (0 : ℝ) 1 :=
  StrictMono.orderIsoOfSurjective qF qF_strictMono qF_surj

/-- The normal quantile function on the open unit interval (zero outside). -/
noncomputable def qInv (u : ℝ) : ℝ := if h : u ∈ Set.Ioo (0 : ℝ) 1 then qIso.symm ⟨u, h⟩ else 0

lemma qInv_spec {u : ℝ} (hu : u ∈ Set.Ioo (0 : ℝ) 1) : stdNormalCdf (qInv u) = u := by
  unfold qInv
  rw [dif_pos hu]
  have h := StrictMono.orderIsoOfSurjective_self_symm_apply qF qF_strictMono qF_surj ⟨u, hu⟩
  have h2 : ((qF (qIso.symm ⟨u, hu⟩)) : ℝ) = u := by
    unfold qIso; rw [h]
  exact h2

lemma qInv_cdf (z : ℝ) : qInv (stdNormalCdf z) = z := by
  have hu : stdNormalCdf z ∈ Set.Ioo (0 : ℝ) 1 := ⟨g_cdf_pos z, g_cdf_lt_one z⟩
  exact q_cdf_strictMono.injective (qInv_spec hu)

lemma qInv_continuousOn : ContinuousOn qInv (Set.Ioo (0 : ℝ) 1) := by
  rw [continuousOn_iff_continuous_restrict]
  refine (qIso.symm.continuous).congr (fun x => ?_)
  show qIso.symm x = qInv x
  unfold qInv
  rw [dif_pos x.2]

lemma qInv_deriv {u : ℝ} (hu : u ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt qInv (stdNormalPdf (qInv u))⁻¹ u := by
  have hcont : ContinuousAt qInv u :=
    qInv_continuousOn.continuousAt (Ioo_mem_nhds hu.1 hu.2)
  apply HasDerivAt.of_local_left_inverse hcont (g_cdf_deriv (qInv u)) (g_pdf_pos _).ne'
  filter_upwards [Ioo_mem_nhds hu.1 hu.2] with y hy
  exact qInv_spec hy

end LostSalesRQ

namespace LostSalesRQ

open MeasureTheory Set Real Filter Topology Finset

lemma q_hd_pm0 (μ : ℝ) : HasDerivAt (fun t => poisMass t 0) (-poisMass μ 0) μ := by
  have h1 : HasDerivAt (fun t : ℝ => Real.exp (-t)) (Real.exp (-μ) * (-1)) μ :=
    (hasDerivAt_neg' μ).exp
  have hfun : (fun t => poisMass t 0) = fun t : ℝ => Real.exp (-t) := by
    funext t; unfold poisMass; simp
  rw [hfun]
  refine h1.congr_deriv ?_
  unfold poisMass; simp

lemma q_hd_pm (μ : ℝ) (i : ℕ) :
    HasDerivAt (fun t => poisMass t (i + 1)) (poisMass μ i - poisMass μ (i + 1)) μ := by
  have h1 : HasDerivAt (fun t : ℝ => Real.exp (-t)) (Real.exp (-μ) * (-1)) μ :=
    (hasDerivAt_neg' μ).exp
  have h2 : HasDerivAt (fun t : ℝ => t ^ (i + 1)) (((i + 1 : ℕ) : ℝ) * μ ^ i) μ := by
    simpa using hasDerivAt_pow (i + 1) μ
  have h3 := (h1.fun_mul h2).div_const ((Nat.factorial (i + 1) : ℕ) : ℝ)
  have hfun : (fun t => poisMass t (i + 1))
      = fun t => Real.exp (-t) * t ^ (i + 1) / ((Nat.factorial (i + 1) : ℕ) : ℝ) := by
    funext t; rfl
  rw [hfun]
  refine h3.congr_deriv ?_
  unfold poisMass
  rw [Nat.factorial_succ]
  push_cast
  have hf : (Nat.factorial i : ℝ) ≠ 0 := by positivity
  have hi : (i : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

lemma q_hd_pc (μ : ℝ) (j : ℕ) : HasDerivAt (fun t => poisCdf t j) (-poisMass μ j) μ := by
  induction j with
  | zero =>
    have : (fun t => poisCdf t 0) = fun t => poisMass t 0 := by funext t; exact pc_zero t
    rw [this]; exact q_hd_pm0 μ
  | succ n ih =>
    have : (fun t => poisCdf t (n + 1)) = fun t => poisCdf t n + poisMass t (n + 1) := by
      funext t; exact pc_succ t n
    rw [this]
    exact (ih.add (q_hd_pm μ n)).congr_deriv (by ring)

lemma q_hd_pm' {μ : ℝ} (hμ : 0 < μ) (n : ℕ) :
    HasDerivAt (fun t => poisMass t n) (((n : ℝ) / μ - 1) * poisMass μ n) μ := by
  cases n with
  | zero => exact (q_hd_pm0 μ).congr_deriv (by simp)
  | succ m =>
    refine (q_hd_pm μ m).congr_deriv ?_
    have h := pm_succ μ m
    push_cast
    field_simp
    linarith

lemma q_hasSum {μ : ℝ} (hμ : 0 ≤ μ) : HasSum (fun n => poisMass μ n) 1 := by
  have h := (NormedSpace.expSeries_div_hasSum_exp μ).mul_left (Real.exp (-μ))
  have e : Real.exp (-μ) * NormedSpace.exp μ = 1 := by
    rw [← Real.exp_eq_exp_ℝ, ← Real.exp_add]; simp
  rw [e] at h
  have e2 : (fun n => poisMass μ n) = fun n => Real.exp (-μ) * (μ ^ n / (n.factorial : ℝ)) := by
    funext n; unfold poisMass; ring
  rw [e2]; exact h

lemma q_pc_lt_one {μ : ℝ} (hμ : 0 < μ) (n : ℕ) : poisCdf μ n < 1 := by
  have h := sum_le_hasSum (range (n + 2)) (fun i _ => (pm_pos hμ i).le) (q_hasSum hμ.le)
  have h2 : poisCdf μ (n + 1) ≤ 1 := h
  rw [pc_succ] at h2
  have := pm_pos hμ (n + 1)
  linarith

/-- Residual mean of the Erlang time Γ(n+1, 1) beyond t. -/
noncomputable def mGam (n : ℕ) (t : ℝ) : ℝ :=
  ((n : ℝ) + 1) - t + t * (poisMass t n / poisCdf t n)

lemma q_ES {μ : ℝ} (hμ : 0 < μ) (n : ℕ) :
    expectedShortfall μ (n + 1) = poisCdf μ n * mGam n μ := by
  have hF := pc_pos hμ n
  have hs := sum_i_pm μ (n + 1)
  have hsucc := pm_succ μ n
  have hc := pc_succ μ n
  have e : expectedShortfall μ (n + 1) =
      ((n : ℝ) + 1) * poisCdf μ (n + 1) - ∑ i ∈ range (n + 1 + 1), (i : ℝ) * poisMass μ i := by
    unfold expectedShortfall poisCdf
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro i _; push_cast; ring
  rw [e, hs]
  unfold mGam
  rw [hc]
  field_simp
  linear_combination hsucc

lemma q_mGam_ge {μ : ℝ} (hμ : 0 < μ) (n : ℕ) : 1 ≤ mGam n μ := by
  have hF := pc_pos hμ n
  have hES := q_ES hμ n
  have hge : poisCdf μ n ≤ expectedShortfall μ (n + 1) := by
    unfold expectedShortfall poisCdf
    rw [Finset.sum_range_succ (fun i => ((((n + 1 : ℕ) : ℝ)) - (i : ℝ)) * poisMass μ i) (n + 1)]
    push_cast
    simp only [sub_self, zero_mul, add_zero]
    apply Finset.sum_le_sum
    intro i hi
    have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 - (i : ℝ) := by
      have : (i : ℝ) ≤ n := by exact_mod_cast hi'
      linarith
    have := (pm_pos hμ i).le
    nlinarith
  rw [hES] at hge
  by_contra hc
  push Not at hc
  have := mul_lt_mul_of_pos_left hc hF
  linarith

lemma q_mGam_deriv {μ : ℝ} (hμ : 0 < μ) (n : ℕ) :
    HasDerivAt (mGam n) (poisMass μ n / poisCdf μ n * mGam n μ - 1) μ := by
  have hF := pc_pos hμ n
  have hp := q_hd_pm' hμ n
  have hc := q_hd_pc μ n
  have h1 := ((hasDerivAt_id μ).mul (hp.div hc hF.ne'))
  have h2 := ((hasDerivAt_const μ ((n : ℝ) + 1)).sub (hasDerivAt_id μ)).add h1
  unfold mGam
  refine h2.congr_deriv ?_
  simp only [id, Pi.div_apply]
  field_simp
  ring

end LostSalesRQ

namespace LostSalesRQ

open MeasureTheory Set Real Filter Topology

/-! ### One-variable sign lemmas -/

/-- A function on (0,∞) that vanishes at 1 and has negative derivative off 1 is positive on
(0,1) and negative on (1,∞). -/
lemma q_sign_of_deriv (f f' : ℝ → ℝ) (hd : ∀ x, 0 < x → HasDerivAt f (f' x) x)
    (hneg : ∀ x, 0 < x → x ≠ 1 → f' x < 0) (h1 : f 1 = 0) :
    (∀ x, 0 < x → x < 1 → 0 < f x) ∧ (∀ x, 1 < x → f x < 0) := by
  constructor
  · intro x hx0 hx1
    have hanti : StrictAntiOn f (Set.Icc x 1) := by
      apply strictAntiOn_of_deriv_neg (convex_Icc x 1)
      · intro y hy
        exact (hd y (lt_of_lt_of_le hx0 hy.1)).continuousAt.continuousWithinAt
      · intro y hy
        rw [interior_Icc] at hy
        rw [(hd y (lt_trans hx0 hy.1)).deriv]
        exact hneg y (lt_trans hx0 hy.1) (ne_of_lt hy.2)
    have := hanti ⟨le_rfl, hx1.le⟩ ⟨hx1.le, le_rfl⟩ hx1
    rw [h1] at this
    exact this
  · intro x hx1
    have hanti : StrictAntiOn f (Set.Icc 1 x) := by
      apply strictAntiOn_of_deriv_neg (convex_Icc 1 x)
      · intro y hy
        exact (hd y (by linarith [hy.1])).continuousAt.continuousWithinAt
      · intro y hy
        rw [interior_Icc] at hy
        rw [(hd y (by linarith [hy.1])).deriv]
        exact hneg y (by linarith [hy.1]) (ne_of_gt hy.1)
    have := hanti ⟨le_rfl, hx1.le⟩ ⟨hx1.le, le_rfl⟩ hx1
    rw [h1] at this
    exact this

/-- N(ν) = -ν + 1/ν + 2 log ν. -/
noncomputable def qN (x : ℝ) : ℝ := -x + 1 / x + 2 * Real.log x

lemma qN_sign : (∀ x, 0 < x → x < 1 → 0 < qN x) ∧ (∀ x, 1 < x → qN x < 0) := by
  apply q_sign_of_deriv qN (fun x => -(1 - 1 / x) ^ 2)
  · intro x hx
    have h := (((hasDerivAt_id x).neg).add ((hasDerivAt_id x).inv hx.ne')).add
      ((Real.hasDerivAt_log hx.ne').const_mul 2)
    unfold qN
    refine (h.congr_deriv ?_).congr_of_eventuallyEq ?_
    · simp only [id]; field_simp; ring
    · filter_upwards with y
      simp [one_div]
  · intro x hx hx1
    have : 1 - 1 / x ≠ 0 := by
      intro h; apply hx1; field_simp at h; linarith
    have := pow_pos (abs_pos.mpr this) 2
    rw [sq_abs] at this
    linarith
  · unfold qN; simp

/-- S(ν) = ν - 1 - log ν - (ν-1)²/2. -/
noncomputable def qS (x : ℝ) : ℝ := x - 1 - Real.log x - (x - 1) ^ 2 / 2

lemma qS_sign : (∀ x, 0 < x → x < 1 → 0 < qS x) ∧ (∀ x, 1 < x → qS x < 0) := by
  apply q_sign_of_deriv qS (fun x => -(x - 1) ^ 2 / x)
  · intro x hx
    have h := (((hasDerivAt_id x).sub_const 1).sub (Real.hasDerivAt_log hx.ne')).sub
      ((((hasDerivAt_id x).sub_const 1).pow 2).div_const 2)
    unfold qS
    refine h.congr_deriv ?_
    simp only [id]; field_simp; ring
  · intro x hx hx1
    have : 0 < (x - 1) ^ 2 := by
      have : x - 1 ≠ 0 := sub_ne_zero.mpr hx1
      positivity
    have := div_pos this hx
    rw [neg_div]
    linarith
  · unfold qS; simp

/-- Ξ(ν) = 1 - ν² + 2 ν log ν. -/
noncomputable def qXi (x : ℝ) : ℝ := 1 - x ^ 2 + 2 * x * Real.log x

lemma qXi_sign : (∀ x, 0 < x → x < 1 → 0 < qXi x) ∧ (∀ x, 1 < x → qXi x < 0) := by
  apply q_sign_of_deriv qXi (fun x => 2 * (1 - x + Real.log x))
  · intro x hx
    have h := ((hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).pow 2)).add
      (((hasDerivAt_id x).const_mul 2).mul (Real.hasDerivAt_log hx.ne'))
    unfold qXi
    refine h.congr_deriv ?_
    simp only [id]; field_simp; ring
  · intro x hx hx1
    have := Real.log_lt_sub_one_of_pos hx hx1
    linarith
  · unfold qXi; simp

/-- ρ(ν) = (ν - 1 - log ν)/(ν - 1)². -/
noncomputable def qRho (x : ℝ) : ℝ := (x - 1 - Real.log x) / (x - 1) ^ 2

lemma qRho_pos {x : ℝ} (hx : 0 < x) (hx1 : x ≠ 1) : 0 < qRho x := by
  unfold qRho
  have h1 := Real.log_lt_sub_one_of_pos hx hx1
  have h2 : 0 < (x - 1) ^ 2 := by
    have : x - 1 ≠ 0 := sub_ne_zero.mpr hx1
    positivity
  exact div_pos (by linarith) h2

lemma qRho_deriv {x : ℝ} (hx : 0 < x) (hx1 : x ≠ 1) :
    HasDerivAt qRho (qN x / (x - 1) ^ 3) x := by
  have hne : (x - 1) ^ 2 ≠ 0 := by
    have : x - 1 ≠ 0 := sub_ne_zero.mpr hx1
    positivity
  have hA : HasDerivAt (fun y => y - 1 - Real.log y) (1 - x⁻¹) x :=
    ((hasDerivAt_id x).sub_const 1).sub (Real.hasDerivAt_log hx.ne')
  have hB : HasDerivAt (fun y => (y - 1) ^ 2) (2 * (x - 1)) x := by
    have := ((hasDerivAt_id x).sub_const 1).pow 2
    refine this.congr_deriv ?_
    simp
  have h := hA.div hB hne
  unfold qRho
  refine h.congr_deriv ?_
  have h3 : x - 1 ≠ 0 := sub_ne_zero.mpr hx1
  unfold qN
  field_simp
  ring

lemma qRho_gt_half {x : ℝ} (hx : 0 < x) (hx1 : x < 1) : 1 / 2 < qRho x := by
  have hS := qS_sign.1 x hx hx1
  unfold qS at hS
  unfold qRho
  have h2 : 0 < (x - 1) ^ 2 := by
    have : x - 1 ≠ 0 := by linarith
    positivity
  rw [lt_div_iff₀ h2]
  linarith

lemma qRho_lt_half {x : ℝ} (hx1 : 1 < x) : qRho x < 1 / 2 := by
  have hS := qS_sign.2 x hx1
  unfold qS at hS
  unfold qRho
  have h2 : 0 < (x - 1) ^ 2 := by
    have : x - 1 ≠ 0 := by linarith
    positivity
  rw [div_lt_iff₀ h2]
  linarith

lemma qRho_anti_lt : StrictAntiOn qRho (Set.Ioo 0 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioo 0 1)
  · intro y hy
    exact (qRho_deriv hy.1 (ne_of_lt hy.2)).continuousAt.continuousWithinAt
  · intro y hy
    rw [interior_Ioo] at hy
    rw [(qRho_deriv hy.1 (ne_of_lt hy.2)).deriv]
    have hN := qN_sign.1 y hy.1 hy.2
    have h3 : (y - 1) ^ 3 < 0 := by
      have : y - 1 < 0 := by linarith [hy.2]
      have := pow_pos (neg_pos.mpr this) 3
      nlinarith [this]
    exact div_neg_of_pos_of_neg hN h3

lemma qRho_anti_gt : StrictAntiOn qRho (Set.Ioi 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi 1)
  · intro y hy
    exact (qRho_deriv (by linarith [mem_Ioi.mp hy]) (ne_of_gt hy)).continuousAt.continuousWithinAt
  · intro y hy
    rw [interior_Ioi] at hy
    have hy1 : 1 < y := hy
    rw [(qRho_deriv (by linarith) (ne_of_gt hy1)).deriv]
    have hN := qN_sign.2 y hy1
    have h3 : 0 < (y - 1) ^ 3 := by
      have : 0 < y - 1 := by linarith
      positivity
    exact div_neg_of_neg_of_pos hN h3

/-- ρ is strictly decreasing across (0,1) ∪ (1,∞). -/
lemma qRho_lt {x y : ℝ} (hx : 0 < x) (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hxy : x < y) :
    qRho y < qRho x := by
  rcases lt_or_gt_of_ne hx1 with hx1' | hx1'
  · rcases lt_or_gt_of_ne hy1 with hy1' | hy1'
    · exact qRho_anti_lt ⟨hx, hx1'⟩ ⟨by linarith, hy1'⟩ hxy
    · linarith [qRho_gt_half hx hx1', qRho_lt_half hy1']
  · have hy1' : 1 < y := by linarith
    exact qRho_anti_gt (mem_Ioi.mpr hx1') (mem_Ioi.mpr hy1') hxy

end LostSalesRQ

namespace LostSalesRQ

open MeasureTheory Set Real Filter Topology

/-- ψ(t) = K log(K/t) - K + t. -/
noncomputable def qPsi (K t : ℝ) : ℝ := K * Real.log (K / t) - K + t

/-- The signed root ζ(t) = sgn(K - t) √(2 ψ(t)). -/
noncomputable def qZeta (K t : ℝ) : ℝ :=
  if t ≤ K then Real.sqrt (2 * qPsi K t) else -Real.sqrt (2 * qPsi K t)

lemma qPsi_eq {K t : ℝ} (hK : 0 < K) (ht : 0 < t) :
    qPsi K t = K * (t / K - 1 - Real.log (t / K)) := by
  unfold qPsi
  have : Real.log (K / t) = -Real.log (t / K) := by rw [← Real.log_inv, inv_div]
  rw [this]; field_simp; ring

lemma qPsi_nonneg {K t : ℝ} (hK : 0 < K) (ht : 0 < t) : 0 ≤ qPsi K t := by
  rw [qPsi_eq hK ht]
  have := Real.log_le_sub_one_of_pos (div_pos ht hK)
  apply mul_nonneg hK.le; linarith

lemma qPsi_pos {K t : ℝ} (hK : 0 < K) (ht : 0 < t) (hne : t ≠ K) : 0 < qPsi K t := by
  rw [qPsi_eq hK ht]
  have h1 : t / K ≠ 1 := by
    intro h; apply hne; field_simp at h; linarith
  have := Real.log_lt_sub_one_of_pos (div_pos ht hK) h1
  apply mul_pos hK; linarith

lemma qPsi_self {K : ℝ} (hK : 0 < K) : qPsi K K = 0 := by
  unfold qPsi; simp [div_self hK.ne']

lemma qPsi_deriv {K t : ℝ} (hK : 0 < K) (ht : 0 < t) :
    HasDerivAt (qPsi K) (1 - K / t) t := by
  have h1 : HasDerivAt (fun y : ℝ => K / y) ((0 * t - K * 1) / t ^ 2) t :=
    (hasDerivAt_const t K).div (hasDerivAt_id' t) ht.ne'
  have h2 := ((h1.log (div_pos hK ht).ne').const_mul K).sub_const K
  have h3 := h2.add (hasDerivAt_id' t)
  unfold qPsi
  refine h3.congr_deriv ?_
  field_simp
  ring

lemma qZeta_abs (K t : ℝ) : |qZeta K t| = Real.sqrt (2 * qPsi K t) := by
  unfold qZeta
  split_ifs
  · exact abs_of_nonneg (Real.sqrt_nonneg _)
  · rw [abs_neg]; exact abs_of_nonneg (Real.sqrt_nonneg _)

lemma qZeta_sq {K t : ℝ} (hK : 0 < K) (ht : 0 < t) : qZeta K t ^ 2 = 2 * qPsi K t := by
  rw [← sq_abs, qZeta_abs, Real.sq_sqrt (by linarith [qPsi_nonneg hK ht])]

lemma qZeta_pos {K t : ℝ} (hK : 0 < K) (ht : 0 < t) (hlt : t < K) : 0 < qZeta K t := by
  unfold qZeta
  rw [if_pos hlt.le]
  exact Real.sqrt_pos.mpr (by linarith [qPsi_pos hK ht (ne_of_lt hlt)])

lemma qZeta_neg {K t : ℝ} (hK : 0 < K) (hgt : K < t) : qZeta K t < 0 := by
  unfold qZeta
  rw [if_neg (not_le.mpr hgt)]
  have := Real.sqrt_pos.mpr (by linarith [qPsi_pos hK (by linarith) (ne_of_gt hgt)] :
    (0 : ℝ) < 2 * qPsi K t)
  linarith

lemma qZeta_self {K : ℝ} (hK : 0 < K) : qZeta K K = 0 := by
  unfold qZeta; rw [if_pos le_rfl, qPsi_self hK]; simp

lemma qZeta_deriv {K t : ℝ} (hK : 0 < K) (ht : 0 < t) (hne : t ≠ K) :
    HasDerivAt (qZeta K) ((1 - K / t) / qZeta K t) t := by
  have hψ := qPsi_pos hK ht hne
  have h := ((qPsi_deriv hK ht).const_mul 2).sqrt (by linarith : 2 * qPsi K t ≠ 0)
  have hs : 0 < Real.sqrt (2 * qPsi K t) := Real.sqrt_pos.mpr (by linarith)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hev : qZeta K =ᶠ[𝓝 t] fun s => Real.sqrt (2 * qPsi K s) := by
      filter_upwards [Iio_mem_nhds hlt] with s hs
      unfold qZeta; rw [if_pos (le_of_lt hs)]
    refine (h.congr_of_eventuallyEq hev).congr_deriv ?_
    have hz : qZeta K t = Real.sqrt (2 * qPsi K t) := by unfold qZeta; rw [if_pos hlt.le]
    rw [hz]
    field_simp
  · have hev : qZeta K =ᶠ[𝓝 t] fun s => -Real.sqrt (2 * qPsi K s) := by
      filter_upwards [Ioi_mem_nhds hgt] with s hs
      unfold qZeta; rw [if_neg (not_le.mpr hs)]
    refine (h.neg.congr_of_eventuallyEq hev).congr_deriv ?_
    have hz : qZeta K t = -Real.sqrt (2 * qPsi K t) := by
      unfold qZeta; rw [if_neg (not_le.mpr hgt)]
    rw [hz]
    field_simp

lemma qZeta_contAt {K t : ℝ} (hK : 0 < K) (ht : 0 < t) : ContinuousAt (qZeta K) t := by
  by_cases hne : t = K
  · subst hne
    show Tendsto (qZeta t) (𝓝 t) (𝓝 (qZeta t t))
    rw [qZeta_self hK, tendsto_zero_iff_abs_tendsto_zero]
    have hfun : (abs ∘ qZeta t) = fun s => Real.sqrt (2 * qPsi t s) := by
      funext s; exact qZeta_abs t s
    rw [hfun]
    have hc : ContinuousAt (fun s => Real.sqrt (2 * qPsi t s)) t :=
      ((qPsi_deriv hK hK).continuousAt.const_mul 2).sqrt
    have := hc.tendsto
    rwa [qPsi_self hK, mul_zero, Real.sqrt_zero] at this
  · exact (qZeta_deriv hK ht hne).continuousAt

lemma q_phi_zeta {K t : ℝ} (hK : 0 < K) (ht : 0 < t) :
    stdNormalPdf (qZeta K t) = Real.exp (-(qPsi K t)) / Real.sqrt (2 * Real.pi) := by
  unfold stdNormalPdf
  rw [qZeta_sq hK ht]
  congr 2
  ring

lemma q_exp_psi (n : ℕ) {t : ℝ} (ht : 0 < t) :
    Real.exp (-(qPsi ((n : ℝ) + 1) t)) =
      (t / ((n : ℝ) + 1)) ^ (n + 1) * Real.exp ((n : ℝ) + 1 - t) := by
  have hK : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hν : 0 < t / ((n : ℝ) + 1) := div_pos ht hK
  have e1 : -(qPsi ((n : ℝ) + 1) t) =
      ((n + 1 : ℕ) : ℝ) * Real.log (t / ((n : ℝ) + 1)) + ((n : ℝ) + 1 - t) := by
    unfold qPsi
    have : Real.log (((n : ℝ) + 1) / t) = -Real.log (t / ((n : ℝ) + 1)) := by
      rw [← Real.log_inv, inv_div]
    rw [this]; push_cast; ring
  rw [e1, Real.exp_add, ← Real.log_pow, Real.exp_log (pow_pos hν _)]

/-- The constant C = √(2π) K^K e^{-K} / (K-1)!. -/
noncomputable def qC (n : ℕ) : ℝ :=
  Real.sqrt (2 * Real.pi) * ((n : ℝ) + 1) ^ (n + 1) * Real.exp (-((n : ℝ) + 1)) /
    (Nat.factorial n : ℝ)

lemma qC_pos (n : ℕ) : 0 < qC n := by unfold qC; positivity

lemma q_pm_zeta (n : ℕ) {t : ℝ} (ht : 0 < t) :
    poisMass t n = qC n / t * stdNormalPdf (qZeta ((n : ℝ) + 1) t) := by
  have hK : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [q_phi_zeta hK ht, q_exp_psi n ht]
  unfold poisMass qC
  have hs : 0 < Real.sqrt (2 * Real.pi) := by positivity
  have he : Real.exp ((n : ℝ) + 1 - t) = Real.exp (-t) / Real.exp (-((n : ℝ) + 1)) := by
    rw [eq_div_iff (Real.exp_pos _).ne', ← Real.exp_add]; ring_nf
  rw [he, div_pow, pow_succ]
  have h1 := Real.exp_pos (-((n : ℝ) + 1))
  field_simp
  ring

/-- D(t) = F_n(t) - Φ(ζ(t)). -/
noncomputable def qD (n : ℕ) (t : ℝ) : ℝ :=
  poisCdf t n - stdNormalCdf (qZeta ((n : ℝ) + 1) t)

/-- W(t) = (K - t)/ζ(t). -/
noncomputable def qW (K t : ℝ) : ℝ := (K - t) / qZeta K t

lemma qD_deriv (n : ℕ) {t : ℝ} (ht : 0 < t) (hne : t ≠ (n : ℝ) + 1) :
    HasDerivAt (qD n)
      (stdNormalPdf (qZeta ((n : ℝ) + 1) t) / t * (qW ((n : ℝ) + 1) t - qC n)) t := by
  have hK : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hz := qZeta_deriv hK ht hne
  have h := (q_hd_pc t n).sub ((g_cdf_deriv (qZeta ((n : ℝ) + 1) t)).comp t hz)
  unfold qD
  refine h.congr_deriv ?_
  rw [q_pm_zeta n ht]
  unfold qW
  have hzne : qZeta ((n : ℝ) + 1) t ≠ 0 := by
    rcases lt_or_gt_of_ne hne with h1 | h1
    · exact (qZeta_pos hK ht h1).ne'
    · exact (qZeta_neg hK h1).ne
  field_simp
  ring

lemma qD_contAt (n : ℕ) {t : ℝ} (ht : 0 < t) : ContinuousAt (qD n) t := by
  have hK : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  exact (q_hd_pc t n).continuousAt.sub
    (q_cdf_cont.continuousAt.comp (qZeta_contAt hK ht))

lemma qW_pos {K t : ℝ} (hK : 0 < K) (ht : 0 < t) (hne : t ≠ K) : 0 < qW K t := by
  unfold qW
  rcases lt_or_gt_of_ne hne with h1 | h1
  · exact div_pos (by linarith) (qZeta_pos hK ht h1)
  · exact div_pos_of_neg_of_neg (by linarith) (qZeta_neg hK h1)

lemma qW_sq {K t : ℝ} (hK : 0 < K) (ht : 0 < t) (hne : t ≠ K) :
    qW K t ^ 2 = K / (2 * qRho (t / K)) := by
  have hν1 : t / K - 1 ≠ 0 := by
    intro h; apply hne; field_simp at h; linarith
  have hν : 0 < t / K := div_pos ht hK
  have hnum : t / K - 1 - Real.log (t / K) ≠ 0 := by
    have := Real.log_lt_sub_one_of_pos hν (by intro h; apply hν1; rw [h]; ring)
    linarith
  unfold qW
  rw [div_pow, qZeta_sq hK ht, qPsi_eq hK ht]
  unfold qRho
  have hKt : K - t = -(K * (t / K - 1)) := by field_simp; ring
  rw [hKt]
  field_simp

lemma qW_lt {K t₁ t₂ : ℝ} (hK : 0 < K) (h1 : 0 < t₁) (hne1 : t₁ ≠ K) (hne2 : t₂ ≠ K)
    (h12 : t₁ < t₂) : qW K t₁ < qW K t₂ := by
  have h2 : 0 < t₂ := by linarith
  have hν1 : 0 < t₁ / K := div_pos h1 hK
  have hν1' : t₁ / K ≠ 1 := by intro h; apply hne1; field_simp at h; linarith
  have hν2' : t₂ / K ≠ 1 := by intro h; apply hne2; field_simp at h; linarith
  have hlt : t₁ / K < t₂ / K := div_lt_div_of_pos_right h12 hK
  have hρ := qRho_lt hν1 hν1' hν2' hlt
  have hρ2 := qRho_pos (div_pos h2 hK) hν2'
  have hsq : qW K t₁ ^ 2 < qW K t₂ ^ 2 := by
    rw [qW_sq hK h1 hne1, qW_sq hK h2 hne2]
    apply div_lt_div_of_pos_left hK (by positivity) (by linarith)
  exact (pow_lt_pow_iff_left₀ (qW_pos hK h1 hne1).le (qW_pos hK h2 hne2).le
    (by norm_num : (2 : ℕ) ≠ 0)).mp hsq

end LostSalesRQ

namespace LostSalesRQ

open MeasureTheory Set Real Filter Topology

lemma q_pc_zero (n : ℕ) : poisCdf 0 n = 1 := by
  induction n with
  | zero => rw [pc_zero]; unfold poisMass; simp
  | succ m ih => rw [pc_succ, ih]; unfold poisMass; simp

lemma q_log_le_half {x : ℝ} (hx : 0 < x) : Real.log x ≤ x / 2 := by
  have h := Real.log_le_sub_one_of_pos (half_pos hx)
  rw [Real.log_div hx.ne' (by norm_num)] at h
  have h2 := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num)
  linarith

lemma qZeta_tendsto0 {K : ℝ} (hK : 0 < K) : Tendsto (qZeta K) (𝓝[>] 0) atTop := by
  rw [tendsto_atTop]
  intro M
  set δ := K * Real.exp (-(1 + M ^ 2 / (2 * K))) with hδ
  have hδ0 : 0 < δ := by positivity
  have hδK : δ < K := by
    have : Real.exp (-(1 + M ^ 2 / (2 * K))) < 1 := by
      rw [Real.exp_lt_one_iff]; have : 0 ≤ M ^ 2 / (2 * K) := by positivity
      linarith
    nlinarith
  filter_upwards [Ioo_mem_nhdsGT hδ0] with t ht
  have ht0 : 0 < t := ht.1
  have htK : t < K := lt_trans ht.2 hδK
  have hν : t / K < Real.exp (-(1 + M ^ 2 / (2 * K))) := by
    rw [div_lt_iff₀ hK]; linarith [ht.2]
  have hlog : Real.log (t / K) < -(1 + M ^ 2 / (2 * K)) := by
    rw [Real.log_lt_iff_lt_exp (div_pos ht0 hK)]; exact hν
  have hψ : M ^ 2 / 2 ≤ qPsi K t := by
    rw [qPsi_eq hK ht0]
    have hpos : 0 < t / K := div_pos ht0 hK
    have h1 : M ^ 2 / (2 * K) ≤ t / K - 1 - Real.log (t / K) := by linarith
    have h2 := mul_le_mul_of_nonneg_left h1 hK.le
    have e : K * (M ^ 2 / (2 * K)) = M ^ 2 / 2 := by field_simp
    linarith
  unfold qZeta
  rw [if_pos htK.le]
  calc M ≤ |M| := le_abs_self M
    _ = Real.sqrt (M ^ 2) := (Real.sqrt_sq_eq_abs M).symm
    _ ≤ Real.sqrt (2 * qPsi K t) := Real.sqrt_le_sqrt (by linarith)

lemma qZeta_tendstoTop {K : ℝ} (hK : 0 < K) : Tendsto (qZeta K) atTop atBot := by
  rw [tendsto_atBot]
  intro M
  filter_upwards [eventually_gt_atTop (max K (M ^ 2 + 2 * K))] with t ht
  have htK : K < t := lt_of_le_of_lt (le_max_left _ _) ht
  have htM : M ^ 2 + 2 * K < t := lt_of_le_of_lt (le_max_right _ _) ht
  have ht0 : 0 < t := by linarith
  have hψ : t / 2 - K ≤ qPsi K t := by
    rw [qPsi_eq hK ht0]
    have h1 := q_log_le_half (div_pos ht0 hK)
    have h2 : t / K / 2 - 1 ≤ t / K - 1 - Real.log (t / K) := by linarith
    have h3 := mul_le_mul_of_nonneg_left h2 hK.le
    have e : K * (t / K / 2 - 1) = t / 2 - K := by field_simp
    linarith
  unfold qZeta
  rw [if_neg (not_le.mpr htK)]
  have h4 : |M| ≤ Real.sqrt (2 * qPsi K t) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by linarith)
  have := neg_abs_le M
  linarith

lemma qD_lim0 (n : ℕ) : Tendsto (qD n) (𝓝[>] 0) (𝓝 0) := by
  have hK : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h1 : Tendsto (fun t => poisCdf t n) (𝓝[>] 0) (𝓝 1) := by
    have := (q_hd_pc 0 n).continuousAt.tendsto
    rw [q_pc_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun t => stdNormalCdf (qZeta ((n : ℝ) + 1) t)) (𝓝[>] 0) (𝓝 1) :=
    q_tendsto_top.comp (qZeta_tendsto0 hK)
  have := h1.sub h2
  rw [sub_self] at this
  exact this

lemma qD_limTop (n : ℕ) : Tendsto (qD n) atTop (𝓝 0) := by
  have hK : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h1 : Tendsto (fun t => poisCdf t n) atTop (𝓝 0) := by
    unfold poisCdf
    have : Tendsto (fun t => ∑ i ∈ Finset.range (n + 1), poisMass t i) atTop
        (𝓝 (∑ i ∈ Finset.range (n + 1), (0 : ℝ))) := by
      apply tendsto_finset_sum
      intro i _
      have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero i).div_const
        (Nat.factorial i : ℝ)
      rw [zero_div] at h
      refine h.congr (fun t => ?_)
      unfold poisMass; ring
    simpa using this
  have h2 : Tendsto (fun t => stdNormalCdf (qZeta ((n : ℝ) + 1) t)) atTop (𝓝 0) :=
    q_tendsto_bot.comp (qZeta_tendstoTop hK)
  have := h1.sub h2
  rw [sub_self] at this
  exact this

lemma q_lt_of_deriv_neg {f : ℝ → ℝ} {a b c : ℝ} (hab : a < b)
    (hcont : ∀ x, a ≤ x → x ≤ b → ContinuousAt f x)
    (hd : ∀ x, a < x → x < b → x ≠ c → ∃ d, HasDerivAt f d x ∧ d < 0) : f b < f a := by
  have key : ∀ a' b', a ≤ a' → a' < b' → b' ≤ b → c ∉ Set.Ioo a' b' → f b' < f a' := by
    intro a' b' h1 h2 h3 hc
    have hanti : StrictAntiOn f (Set.Icc a' b') := by
      apply strictAntiOn_of_deriv_neg (convex_Icc a' b')
      · intro x hx
        exact (hcont x (le_trans h1 hx.1) (le_trans hx.2 h3)).continuousWithinAt
      · intro x hx
        rw [interior_Icc] at hx
        have hxc : x ≠ c := fun h => hc (h ▸ hx)
        obtain ⟨d, hdd, hdneg⟩ := hd x (lt_of_le_of_lt h1 hx.1) (lt_of_lt_of_le hx.2 h3) hxc
        rw [hdd.deriv]
        exact hdneg
    exact hanti ⟨le_rfl, h2.le⟩ ⟨h2.le, le_rfl⟩ h2
  by_cases hc : c ∈ Set.Ioo a b
  · exact lt_trans (key c b hc.1.le hc.2 le_rfl (fun h => lt_irrefl _ h.1))
      (key a c le_rfl hc.1 hc.2.le (fun h => lt_irrefl _ h.2))
  · exact key a b le_rfl hab le_rfl hc

lemma q_lt_of_deriv_pos {f : ℝ → ℝ} {a b c : ℝ} (hab : a < b)
    (hcont : ∀ x, a ≤ x → x ≤ b → ContinuousAt f x)
    (hd : ∀ x, a < x → x < b → x ≠ c → ∃ d, HasDerivAt f d x ∧ 0 < d) : f a < f b := by
  have := q_lt_of_deriv_neg (f := fun x => -f x) (c := c) hab
    (fun x h1 h2 => (hcont x h1 h2).neg)
    (fun x h1 h2 h3 => by
      obtain ⟨d, hdd, hdpos⟩ := hd x h1 h2 h3
      exact ⟨-d, hdd.neg, by linarith⟩)
  have h' : -f b < -f a := this
  linarith

/-- The Alfers-Dinges inequality in the Poisson form: F_n(t) < Φ(ζ(t)). -/
lemma qD_neg (n : ℕ) {t : ℝ} (ht : 0 < t) : qD n t < 0 := by
  set K : ℝ := (n : ℝ) + 1 with hKdef
  have hK : (0 : ℝ) < K := by positivity
  have hcont : ∀ a b x, 0 < a → a ≤ x → x ≤ b → ContinuousAt (qD n) x :=
    fun a b x ha hx _ => qD_contAt n (lt_of_lt_of_le ha hx)
  by_cases hA : ∃ s, t < s ∧ s ≠ K ∧ qW K s ≤ qC n
  · obtain ⟨s, hts, hsK, hWs⟩ := hA
    have hdec : ∀ a b, 0 < a → a < b → b ≤ s → qD n b < qD n a := by
      intro a b ha hab hbs
      apply q_lt_of_deriv_neg hab (fun x hx1 hx2 => hcont a b x ha hx1 hx2) (c := K)
      intro x hax hxb hxK
      have hx0 : 0 < x := lt_trans ha hax
      refine ⟨_, qD_deriv n hx0 hxK, ?_⟩
      have hW : qW K x < qW K s := qW_lt hK hx0 hxK hsK (lt_of_lt_of_le hxb hbs)
      have hφ : 0 < stdNormalPdf (qZeta K x) / x := div_pos (g_pdf_pos _) hx0
      exact mul_neg_of_pos_of_neg hφ (by linarith)
    have hle : qD n (t / 2) ≤ 0 := by
      apply ge_of_tendsto (qD_lim0 n)
      filter_upwards [Ioo_mem_nhdsGT (half_pos ht)] with x hx
      exact (hdec x (t / 2) hx.1 hx.2 (by linarith)).le
    exact lt_of_lt_of_le (hdec (t / 2) t (half_pos ht) (by linarith) hts.le) hle
  · push Not at hA
    have hinc : ∀ a b, t ≤ a → a < b → qD n a < qD n b := by
      intro a b ha hab
      apply q_lt_of_deriv_pos hab (fun x hx1 hx2 => hcont a b x (lt_of_lt_of_le ht ha) hx1 hx2)
        (c := K)
      intro x hax hxb hxK
      have hx0 : 0 < x := by linarith
      refine ⟨_, qD_deriv n hx0 hxK, ?_⟩
      have hW := hA x (by linarith) hxK
      have hφ : 0 < stdNormalPdf (qZeta K x) / x := div_pos (g_pdf_pos _) hx0
      exact mul_pos hφ (by linarith)
    have hle : qD n (t + 1) ≤ 0 := by
      apply ge_of_tendsto (qD_limTop n)
      filter_upwards [eventually_gt_atTop (t + 1)] with x hx
      exact (hinc (t + 1) x (by linarith) hx).le
    exact lt_of_lt_of_le (hinc t (t + 1) le_rfl (by linarith)) hle

lemma qZeta_le {K t : ℝ} (hK : 0 < K) (ht : 0 < t) : qZeta K t ≤ (K - t) / Real.sqrt t := by
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hν : 0 < t / K := div_pos ht hK
  have hid : (K - t) ^ 2 / t - 2 * qPsi K t = K / (t / K) * qXi (t / K) := by
    unfold qPsi qXi
    have : Real.log (K / t) = -Real.log (t / K) := by rw [← Real.log_inv, inv_div]
    rw [this]
    field_simp
    ring
  have hsq : ((K - t) / Real.sqrt t) ^ 2 = (K - t) ^ 2 / t := by
    rw [div_pow, Real.sq_sqrt ht.le]
  have hz2 := qZeta_sq hK ht
  rcases lt_trichotomy t K with hlt | heq | hgt
  · have hX := qXi_sign.1 (t / K) hν (by rw [div_lt_one hK]; exact hlt)
    have hpos : 0 < K / (t / K) * qXi (t / K) := mul_pos (div_pos hK hν) hX
    have hR : 0 < (K - t) / Real.sqrt t := div_pos (by linarith) hst
    have hlt2 : qZeta K t ^ 2 < ((K - t) / Real.sqrt t) ^ 2 := by
      rw [hz2, hsq]; linarith
    have hz0 := (qZeta_pos hK ht hlt).le
    exact ((pow_lt_pow_iff_left₀ hz0 hR.le (by norm_num : (2 : ℕ) ≠ 0)).mp hlt2).le
  · subst heq
    rw [qZeta_self hK, sub_self, zero_div]
  · have hX := qXi_sign.2 (t / K) (by rw [one_lt_div hK]; exact hgt)
    have hneg : K / (t / K) * qXi (t / K) < 0 := mul_neg_of_pos_of_neg (div_pos hK hν) hX
    have hR : (K - t) / Real.sqrt t < 0 := div_neg_of_neg_of_pos (by linarith) hst
    have hlt2 : ((K - t) / Real.sqrt t) ^ 2 < qZeta K t ^ 2 := by
      rw [hz2, hsq]; linarith
    have hz0 := qZeta_neg hK hgt
    nlinarith

/-- The strict quantile bound (G.1): F_n(t) < Φ((K - t)/√t) with K = n + 1. -/
lemma q_quantile (n : ℕ) {t : ℝ} (ht : 0 < t) :
    poisCdf t n < stdNormalCdf ((((n : ℝ) + 1) - t) / Real.sqrt t) := by
  have hK : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h1 := qD_neg n ht
  unfold qD at h1
  have h2 := q_cdf_strictMono.monotone (qZeta_le hK ht)
  linarith

end LostSalesRQ

namespace LostSalesRQ

open MeasureTheory Set Real Filter Topology

/-- Gaussian residual mean m_G(z) = z + φ(z)/Φ(z). -/
noncomputable def qGm (z : ℝ) : ℝ := z + stdNormalPdf z / stdNormalCdf z

lemma qGm_eq (z : ℝ) : qGm z = z + 1 / gU z := by
  unfold qGm gU; rw [one_div_div]

lemma qGm_pos (z : ℝ) : 0 < qGm z := by
  rw [qGm_eq]
  have h1 := g_one_add z
  have h2 := gU_pos z
  have : z + 1 / gU z = (1 + z * gU z) / gU z := by field_simp; ring
  rw [this]; exact div_pos h1 h2

lemma qGm_deriv (z : ℝ) :
    HasDerivAt qGm (1 - stdNormalPdf z / stdNormalCdf z * qGm z) z := by
  have h := (hasDerivAt_id' z).add ((g_pdf_deriv z).div (g_cdf_deriv z) (g_cdf_pos z).ne')
  unfold qGm
  refine h.congr_deriv ?_
  have := (g_cdf_pos z).ne'
  field_simp
  ring

lemma q_I_neg_ge {x : ℝ} (hx : 0 < x) : 1 / x - 1 / x ^ 3 ≤ gI (-x) := by
  rw [g_I_neg_eq]
  have hint1 : IntegrableOn (fun t : ℝ => t ^ 0 * Real.exp (-x * t) -
      1 / 2 * (t ^ 2 * Real.exp (-x * t))) (Ioi 0) :=
    (g_moment_int hx 0).sub ((g_moment_int hx 2).const_mul _)
  have hint2 : IntegrableOn (fun t : ℝ => Real.exp (-x * t) * Real.exp (-(t ^ 2) / 2)) (Ioi 0) := by
    have := (g_exp_int (-x)).integrableOn (s := Ioi 0)
    refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
    rw [← Real.exp_add]; ring_nf
  have hval : ∫ t in Ioi 0, (t ^ 0 * Real.exp (-x * t) - 1 / 2 * (t ^ 2 * Real.exp (-x * t))) =
      1 / x - 1 / x ^ 3 := by
    rw [integral_sub (g_moment_int hx 0) ((g_moment_int hx 2).const_mul _), integral_const_mul,
      g_moment hx 0, g_moment hx 2]
    simp [Nat.factorial]
    field_simp
  rw [← hval]
  apply setIntegral_mono_on hint1 hint2 measurableSet_Ioi
  intro t _
  have h1 := Real.add_one_le_exp (-(t ^ 2) / 2)
  have h2 := (Real.exp_pos (-x * t)).le
  have e : t ^ 0 * Real.exp (-x * t) - 1 / 2 * (t ^ 2 * Real.exp (-x * t)) =
      Real.exp (-x * t) * (-(t ^ 2) / 2 + 1) := by ring
  rw [e]
  exact mul_le_mul_of_nonneg_left h1 h2

lemma qGm_neg_le {x : ℝ} (hx : 1 < x) : qGm (-x) ≤ x / (x ^ 2 - 1) := by
  have hx0 : 0 < x := by linarith
  have hlow := q_I_neg_ge hx0
  have hpos : 0 < 1 / x - 1 / x ^ 3 := by
    have : 1 / x - 1 / x ^ 3 = (x ^ 2 - 1) / x ^ 3 := by field_simp
    rw [this]; apply div_pos (by nlinarith) (by positivity)
  rw [qGm_eq, gU_eq]
  have hinv : 1 / gI (-x) ≤ 1 / (1 / x - 1 / x ^ 3) := one_div_le_one_div_of_le hpos hlow
  have e : -x + 1 / (1 / x - 1 / x ^ 3) = x / (x ^ 2 - 1) := by
    have : x ^ 2 - 1 ≠ 0 := by nlinarith
    field_simp
    ring
  linarith

/-- The Gaussian quantile matching the Poisson tail. -/
noncomputable def qZq (n : ℕ) (t : ℝ) : ℝ := qInv (poisCdf t n)

lemma qZq_mem (n : ℕ) {t : ℝ} (ht : 0 < t) : poisCdf t n ∈ Set.Ioo (0 : ℝ) 1 :=
  ⟨pc_pos ht n, q_pc_lt_one ht n⟩

lemma qZq_spec (n : ℕ) {t : ℝ} (ht : 0 < t) : stdNormalCdf (qZq n t) = poisCdf t n :=
  qInv_spec (qZq_mem n ht)

lemma qZq_deriv (n : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (qZq n) (-poisMass t n / stdNormalPdf (qZq n t)) t := by
  have h := (qInv_deriv (qZq_mem n ht)).comp t (q_hd_pc t n)
  unfold qZq
  refine h.congr_deriv ?_
  have := (g_pdf_pos (qInv (poisCdf t n))).ne'
  field_simp

lemma qZq_lt (n : ℕ) {t : ℝ} (ht : 0 < t) :
    qZq n t < (((n : ℝ) + 1) - t) / Real.sqrt t := by
  have h := q_quantile n ht
  rw [← qZq_spec n ht] at h
  exact q_cdf_strictMono.lt_iff_lt.mp h

/-- T(t) = m_Γ(t) - √t m_G(z(t)). -/
noncomputable def qT (n : ℕ) (t : ℝ) : ℝ := mGam n t - Real.sqrt t * qGm (qZq n t)

lemma qT_deriv (n : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (qT n)
      (poisMass t n / poisCdf t n * mGam n t - 1 -
        (1 / (2 * Real.sqrt t) * qGm (qZq n t) + Real.sqrt t *
          ((1 - stdNormalPdf (qZq n t) / stdNormalCdf (qZq n t) * qGm (qZq n t)) *
            (-poisMass t n / stdNormalPdf (qZq n t))))) t := by
  have h1 := q_mGam_deriv ht n
  have h2 := (Real.hasDerivAt_sqrt ht.ne').mul ((qGm_deriv (qZq n t)).comp t (qZq_deriv n ht))
  exact h1.sub h2

lemma qT_deriv_neg (n : ℕ) {t : ℝ} (ht : 0 < t) (h0 : qT n t = 0) :
    poisMass t n / poisCdf t n * mGam n t - 1 -
        (1 / (2 * Real.sqrt t) * qGm (qZq n t) + Real.sqrt t *
          ((1 - stdNormalPdf (qZq n t) / stdNormalCdf (qZq n t) * qGm (qZq n t)) *
            (-poisMass t n / stdNormalPdf (qZq n t)))) < 0 := by
  set z := qZq n t with hz
  have hF : stdNormalCdf z = poisCdf t n := qZq_spec n ht
  have hFpos := pc_pos ht n
  have hφ := g_pdf_pos z
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hst2 : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
  have hm := qGm_pos z
  have hzw := qZq_lt n ht
  rw [← hz] at hzw
  set w := (((n : ℝ) + 1) - t) / Real.sqrt t with hw
  set m := qGm z with hmdef
  set F := poisCdf t n with hFdef
  set p := poisMass t n with hpdef
  have hT : mGam n t = Real.sqrt t * m := by unfold qT at h0; rw [← hz] at h0; linarith
  have hmG : mGam n t = ((n : ℝ) + 1) - t + t * (p / F) := rfl
  have hmz : m = z + stdNormalPdf z / F := by rw [hmdef]; unfold qGm; rw [hF]
  rw [hF]
  -- the derivative equals (z - w)/q_G - m/(2√t)
  have key : p / F * mGam n t - 1 -
      (1 / (2 * Real.sqrt t) * m + Real.sqrt t *
        ((1 - stdNormalPdf z / F * m) * (-p / stdNormalPdf z))) =
      (z - w) / (stdNormalPdf z / F) - m / (2 * Real.sqrt t) := by
    rw [hw]
    have hwt : (((n : ℝ) + 1) - t) = mGam n t - t * (p / F) := by rw [hmG]; ring
    rw [hwt, hT, hmz]
    field_simp
    linear_combination (2 * p * F ^ 2) * hst2
  rw [key]
  have h1 : (z - w) / (stdNormalPdf z / F) < 0 :=
    div_neg_of_neg_of_pos (by linarith) (div_pos hφ hFpos)
  have h2 : 0 < m / (2 * Real.sqrt t) := by positivity
  linarith

lemma q_pc_le_poly (n : ℕ) {t : ℝ} (ht : 1 ≤ t) :
    poisCdf t n ≤ ((n : ℝ) + 1) * (t ^ n * Real.exp (-t)) := by
  unfold poisCdf
  have h : ∀ i ∈ Finset.range (n + 1), poisMass t i ≤ t ^ n * Real.exp (-t) := by
    intro i hi
    have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    unfold poisMass
    have h1 : t ^ i ≤ t ^ n := pow_le_pow_right₀ ht hi'
    have h2 : (1 : ℝ) ≤ (Nat.factorial i : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero i)
    have h3 := Real.exp_pos (-t)
    rw [div_le_iff₀ (by linarith)]
    have h4 : 0 ≤ t ^ n * Real.exp (-t) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h1 h3.le]
  have := Finset.sum_le_sum h
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
  push_cast at this
  linarith

lemma qT_large (n : ℕ) : ∀ M, ∃ t, M ≤ t ∧ 0 < qT n t := by
  intro M
  set A : ℝ := 12 / 5 * ((n : ℝ) + 1) * Real.sqrt (2 * Real.pi) with hA
  have hA0 : 0 < A := by positivity
  have hlim := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((n : ℝ) + 1) (7 / 25)
    (by norm_num)).const_mul A
  rw [mul_zero] at hlim
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds one_pos))
  set t := max (max M 5) N with htdef
  have ht5 : 5 ≤ t := le_trans (le_max_right _ _) (le_max_left _ _)
  have ht0 : 0 < t := by linarith
  have ht1 : 1 ≤ t := by linarith
  refine ⟨t, le_trans (le_max_left _ _) (le_max_left _ _), ?_⟩
  have hev := hN t (le_max_right _ _)
  rw [show ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast] at hev
  -- y = (6/5) √t
  set y := 6 / 5 * Real.sqrt t with hy
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have hst2 : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht0.le
  have hstle : Real.sqrt t ≤ t := by nlinarith
  have hy2 : y ^ 2 = 36 / 25 * t := by rw [hy]; nlinarith
  have hy1 : 1 < y := by nlinarith
  have hyy : 2 ≤ y ^ 2 := by nlinarith
  have hy0 : 0 < y := by linarith
  -- lower bound for Φ(-y)
  have hΦ : stdNormalPdf y / (2 * y) ≤ stdNormalCdf (-y) := by
    rw [g_cdf_rep, g_pdf_neg]
    have h1 := q_I_neg_ge hy0
    have h2 : 1 / (2 * y) ≤ 1 / y - 1 / y ^ 3 := by
      rw [div_sub_div _ _ hy0.ne' (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have h3 := g_pdf_pos y
    calc stdNormalPdf y / (2 * y) = stdNormalPdf y * (1 / (2 * y)) := by ring
      _ ≤ stdNormalPdf y * gI (-y) := mul_le_mul_of_nonneg_left (le_trans h2 h1) h3.le
  -- Poisson tail is smaller
  have hF := q_pc_le_poly n ht1
  have hpdf : stdNormalPdf y = Real.exp (-(18 / 25 * t)) / Real.sqrt (2 * Real.pi) := by
    unfold stdNormalPdf; rw [hy2]; congr 2; ring
  have hsmall : ((n : ℝ) + 1) * (t ^ n * Real.exp (-t)) < stdNormalPdf y / (2 * y) := by
    rw [hpdf, hy]
    have hs2 : 0 < Real.sqrt (2 * Real.pi) := by positivity
    rw [div_div, lt_div_iff₀ (by positivity)]
    have hexp : Real.exp (-t) = Real.exp (-(7 / 25) * t) * Real.exp (-(18 / 25 * t)) := by
      rw [← Real.exp_add]; ring_nf
    rw [hexp]
    have he := Real.exp_pos (-(18 / 25 * t))
    have h7 := Real.exp_pos (-(7 / 25) * t)
    have hkey : A * (t ^ (n + 1) * Real.exp (-(7 / 25) * t)) < 1 := hev
    have hpow : t ^ n * Real.sqrt t ≤ t ^ (n + 1) := by
      rw [pow_succ]; exact mul_le_mul_of_nonneg_left hstle (by positivity)
    calc ((n : ℝ) + 1) * (t ^ n * (Real.exp (-(7 / 25) * t) * Real.exp (-(18 / 25 * t)))) *
          (Real.sqrt (2 * Real.pi) * (2 * (6 / 5 * Real.sqrt t)))
        = A * (t ^ n * Real.sqrt t * Real.exp (-(7 / 25) * t)) *
            Real.exp (-(18 / 25 * t)) := by rw [hA]; ring
      _ ≤ A * (t ^ (n + 1) * Real.exp (-(7 / 25) * t)) * Real.exp (-(18 / 25 * t)) := by
          gcongr
      _ < 1 * Real.exp (-(18 / 25 * t)) := by
          exact mul_lt_mul_of_pos_right hkey he
      _ = Real.exp (-(18 / 25 * t)) := one_mul _
  have hzlt : qZq n t < -y := by
    have : stdNormalCdf (qZq n t) < stdNormalCdf (-y) := by
      rw [qZq_spec n ht0]; linarith
    exact q_cdf_strictMono.lt_iff_lt.mp this
  -- bound on m_G
  set x := -qZq n t with hxdef
  have hxy : y < x := by linarith
  have hx1 : 1 < x := by linarith
  have hmG := qGm_neg_le hx1
  rw [hxdef, neg_neg] at hmG
  have hmono : x / (x ^ 2 - 1) ≤ y / (y ^ 2 - 1) := by
    rw [div_le_div_iff₀ (by nlinarith) (by nlinarith)]
    nlinarith [mul_pos hy0 (by linarith : (0 : ℝ) < x)]
  have hbound : Real.sqrt t * (y / (y ^ 2 - 1)) < 1 := by
    rw [hy2]
    have hden : 0 < 36 / 25 * t - 1 := by linarith
    rw [hy, mul_div_assoc', div_lt_one hden]
    nlinarith
  have hmGam := q_mGam_ge ht0 n
  unfold qT
  have : Real.sqrt t * qGm (qZq n t) ≤ Real.sqrt t * (y / (y ^ 2 - 1)) :=
    mul_le_mul_of_nonneg_left (le_trans hmG hmono) hst.le
  linarith

lemma qT_pos (n : ℕ) {t : ℝ} (ht : 0 < t) : 0 < qT n t :=
  g2_crossing (qT n) t
    (fun s hs => ⟨_, qT_deriv n (lt_of_lt_of_le ht hs), qT_deriv_neg n (lt_of_lt_of_le ht hs)⟩)
    (qT_large n) t le_rfl

end LostSalesRQ

namespace LostSalesRQ

open MeasureTheory Set Real Filter Topology

lemma q_rank_le (s : ℝ) (hs : 0 ≤ s) (z : ℝ) :
    gaussianRankProfile s ≤
      stdNormalPdf z + z * stdNormalCdf z + s * (1 - stdNormalCdf z) := by
  unfold gaussianRankProfile
  apply ciInf_le ⟨0, ?_⟩ z
  rintro _ ⟨y, rfl⟩
  have h1 : stdNormalPdf y + y * stdNormalCdf y = stdNormalCdf y * qGm y := by
    unfold qGm; have := (g_cdf_pos y).ne'; field_simp; ring
  have h2 := mul_pos (g_cdf_pos y) (qGm_pos y)
  have h3 := g_cdf_lt_one y
  have h4 : 0 ≤ s * (1 - stdNormalCdf y) := mul_nonneg hs (by linarith)
  simp only
  linarith

lemma q_rank_lt_s {s : ℝ} (hs : 0 < s) : gaussianRankProfile s < s := by
  set x := 2 / s + 2 with hx
  have hs2 : 0 < 2 / s := by positivity
  have hx2 : 2 ≤ x := by linarith
  have hx1 : 1 < x := by linarith
  have hm := qGm_neg_le hx1
  have hb : x / (x ^ 2 - 1) < s := by
    have hden : 0 < x ^ 2 - 1 := by nlinarith
    rw [div_lt_iff₀ hden]
    have h2s : 2 / s < x := by linarith
    have : 2 < x * s := (div_lt_iff₀ hs).mp h2s
    nlinarith
  have hle := q_rank_le s hs.le (-x)
  have h1 : stdNormalPdf (-x) + -x * stdNormalCdf (-x) = stdNormalCdf (-x) * qGm (-x) := by
    unfold qGm; have := (g_cdf_pos (-x)).ne'; field_simp; ring
  have hΦ := g_cdf_pos (-x)
  have : stdNormalCdf (-x) * qGm (-x) < stdNormalCdf (-x) * s :=
    mul_lt_mul_of_pos_left (lt_of_le_of_lt hm hb) hΦ
  linarith

lemma q_cost_zero (μ η : ℝ) : expectedShortfall μ 0 + η * poisTail μ 0 = η := by
  unfold expectedShortfall poisTail; simp

lemma q_tail_succ (μ : ℝ) (n : ℕ) : poisTail μ (n + 1) = 1 - poisCdf μ n := rfl

lemma q_cost_succ {μ η : ℝ} (hμ : 0 < μ) (hη : 0 ≤ η) (n : ℕ) :
    Real.sqrt μ * gaussianRankProfile (η / Real.sqrt μ) <
      expectedShortfall μ (n + 1) + η * poisTail μ (n + 1) := by
  have hsμ : 0 < Real.sqrt μ := Real.sqrt_pos.mpr hμ
  set z := qZq n μ with hz
  have hF : stdNormalCdf z = poisCdf μ n := qZq_spec n hμ
  have hFpos := pc_pos hμ n
  have hT := qT_pos n hμ
  unfold qT at hT
  rw [← hz] at hT
  have hle := q_rank_le (η / Real.sqrt μ) (div_nonneg hη hsμ.le) z
  have h1 : stdNormalPdf z + z * stdNormalCdf z = stdNormalCdf z * qGm z := by
    unfold qGm; have := (g_cdf_pos z).ne'; field_simp; ring
  rw [h1, hF] at hle
  have h2 : Real.sqrt μ * gaussianRankProfile (η / Real.sqrt μ) ≤
      poisCdf μ n * (Real.sqrt μ * qGm z) + η * (1 - poisCdf μ n) := by
    have := mul_le_mul_of_nonneg_left hle hsμ.le
    calc Real.sqrt μ * gaussianRankProfile (η / Real.sqrt μ)
        ≤ Real.sqrt μ * (poisCdf μ n * qGm z + η / Real.sqrt μ * (1 - poisCdf μ n)) := this
      _ = poisCdf μ n * (Real.sqrt μ * qGm z) + η * (1 - poisCdf μ n) := by
          field_simp
  have h3 : poisCdf μ n * (Real.sqrt μ * qGm z) < poisCdf μ n * mGam n μ :=
    mul_lt_mul_of_pos_left (by linarith) hFpos
  rw [q_ES hμ n, q_tail_succ]
  linarith

lemma q_cost_ge {μ η : ℝ} (hμ : 0 < μ) (hη : 0 ≤ η) (n : ℕ) (hn : μ ≤ (n : ℝ) + 1) :
    ((n : ℝ) + 1 - μ) * Real.exp (-μ) ≤
      expectedShortfall μ (n + 1) + η * poisTail μ (n + 1) := by
  have hF := pc_pos hμ n
  have hp := pm_pos hμ n
  have hES : expectedShortfall μ (n + 1) = ((n : ℝ) + 1 - μ) * poisCdf μ n + μ * poisMass μ n := by
    rw [q_ES hμ n]; unfold mGam; field_simp
  have hF0 : Real.exp (-μ) ≤ poisCdf μ n := by
    have h0 : poisMass μ 0 = Real.exp (-μ) := by unfold poisMass; simp
    rw [← h0]
    unfold poisCdf
    exact Finset.single_le_sum (fun i _ => (pm_pos hμ i).le)
      (Finset.mem_range.mpr (Nat.succ_pos n))
  have hT : 0 ≤ poisTail μ (n + 1) := by
    rw [q_tail_succ]; linarith [q_pc_lt_one hμ n]
  rw [hES]
  have h1 : ((n : ℝ) + 1 - μ) * Real.exp (-μ) ≤ ((n : ℝ) + 1 - μ) * poisCdf μ n :=
    mul_le_mul_of_nonneg_left hF0 (by linarith)
  have h2 : 0 ≤ μ * poisMass μ n := by positivity
  have h3 : 0 ≤ η * poisTail μ (n + 1) := mul_nonneg hη hT
  linarith

end LostSalesRQ

open LostSalesRQ in
theorem solution (μ η : ℝ) (hμ : 0 < μ) (hη : 1 ≤ η) :
    Real.sqrt μ * gaussianRankProfile (η / Real.sqrt μ) < rankBound μ η := by
  have hsμ : 0 < Real.sqrt μ := Real.sqrt_pos.mpr hμ
  have hη0 : 0 ≤ η := by linarith
  have hs : 0 < η / Real.sqrt μ := div_pos (by linarith) hsμ
  set cost : ℕ → ℝ := fun l => expectedShortfall μ l + η * poisTail μ l with hcost
  set N := ⌈μ + η * Real.exp μ⌉₊ with hN
  obtain ⟨l0, -, hl0⟩ := (Finset.range (N + 1)).exists_min_image cost ⟨0, by simp⟩
  have hc0 : cost 0 = η := q_cost_zero μ η
  have hmin : ∀ l, cost l0 ≤ cost l := by
    intro l
    by_cases hl : l ∈ Finset.range (N + 1)
    · exact hl0 l hl
    · have h0 := hl0 0 (by simp)
      rw [hc0] at h0
      rw [Finset.mem_range, not_lt] at hl
      obtain ⟨n, rfl⟩ : ∃ n, l = n + 1 := ⟨l - 1, by omega⟩
      have hNle : μ + η * Real.exp μ ≤ (N : ℝ) := Nat.le_ceil _
      have hnN : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : N ≤ n)
      have he := Real.exp_pos μ
      have hn : μ ≤ (n : ℝ) + 1 := by nlinarith
      have hge := q_cost_ge hμ hη0 n hn
      have hem : Real.exp (-μ) * Real.exp μ = 1 := by rw [← Real.exp_add]; simp
      have hem0 := Real.exp_pos (-μ)
      have hkey : η ≤ ((n : ℝ) + 1 - μ) * Real.exp (-μ) := by
        have : η * Real.exp μ ≤ (n : ℝ) + 1 - μ := by linarith
        have := mul_le_mul_of_nonneg_right this hem0.le
        nlinarith
      show cost l0 ≤ expectedShortfall μ (n + 1) + η * poisTail μ (n + 1)
      linarith
  have hrank : rankBound μ η = cost l0 := by
    unfold rankBound
    apply le_antisymm (ciInf_le ⟨cost l0, by rintro _ ⟨l, rfl⟩; exact hmin l⟩ l0)
    exact le_ciInf hmin
  rw [hrank]
  cases l0 with
  | zero =>
    rw [hc0]
    have h := q_rank_lt_s hs
    have := mul_lt_mul_of_pos_left h hsμ
    rw [mul_div_cancel₀ η hsμ.ne'] at this
    exact this
  | succ n => exact q_cost_succ hμ hη0 n
