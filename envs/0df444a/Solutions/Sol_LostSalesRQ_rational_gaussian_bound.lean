-- Prove2me | solution 1 for LostSalesRQ.rational_gaussian_bound
-- status  : ACCEPTED   (prove)
-- author  : @Ming Hu
-- created : 2026-11-17T20:28:56.98871+00:00
-- url     : https://prove2.me/submissions/17784ca6-5a13-48bc-9599-e6a26af3e8f2

import Definitions.Def_LostSalesRQ_gaussian
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.IntermediateValue

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

lemma g_I_neg_le {x : ℝ} (hx : 0 < x) : gI (-x) ≤ 1 / x - 1 / x ^ 3 + 3 / x ^ 5 := by
  have m0 := g_moment hx 0
  have m2 := g_moment hx 2
  have m4 := g_moment hx 4
  simp only [pow_zero, one_mul, Nat.factorial, Nat.succ_eq_add_one, zero_add] at m0 m2 m4
  have i0 := g_moment_int hx 0
  have i2 := g_moment_int hx 2
  have i4 := g_moment_int hx 4
  simp only [pow_zero, one_mul] at i0
  have hint2 : IntegrableOn (fun t : ℝ => Real.exp (-x * t) * Real.exp (-(t ^ 2) / 2)) (Ioi 0) := by
    have := (g_exp_int (-x)).integrableOn (s := Ioi 0)
    refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
    rw [← Real.exp_add]; ring_nf
  have hcomb : IntegrableOn (fun t : ℝ => Real.exp (-x * t) - (1 / 2) * (t ^ 2 * Real.exp (-x * t)) +
      (1 / 8) * (t ^ 4 * Real.exp (-x * t))) (Ioi 0) :=
    (i0.sub (i2.const_mul (1 / 2))).add (i4.const_mul (1 / 8))
  have hmono : ∫ t in Ioi 0, Real.exp (-x * t) * Real.exp (-(t ^ 2) / 2) ≤
      ∫ t in Ioi 0, (Real.exp (-x * t) - (1 / 2) * (t ^ 2 * Real.exp (-x * t)) +
        (1 / 8) * (t ^ 4 * Real.exp (-x * t))) := by
    apply setIntegral_mono_on hint2 hcomb measurableSet_Ioi
    intro t _
    have hq := g_exp_quad (by positivity : (0 : ℝ) ≤ t ^ 2 / 2)
    have e : Real.exp (-(t ^ 2) / 2) = Real.exp (-(t ^ 2 / 2)) := by ring_nf
    rw [e]
    have he := Real.exp_pos (-x * t)
    have := mul_le_mul_of_nonneg_left hq he.le
    nlinarith
  have hsplit : ∫ t in Ioi 0, (Real.exp (-x * t) - (1 / 2) * (t ^ 2 * Real.exp (-x * t)) +
      (1 / 8) * (t ^ 4 * Real.exp (-x * t))) =
      (∫ t in Ioi 0, Real.exp (-x * t)) - (1 / 2) * (∫ t in Ioi 0, t ^ 2 * Real.exp (-x * t)) +
        (1 / 8) * (∫ t in Ioi 0, t ^ 4 * Real.exp (-x * t)) := by
    rw [integral_add, integral_sub, integral_const_mul, integral_const_mul]
    · exact i0
    · exact i2.const_mul _
    · exact i0.sub (i2.const_mul _)
    · exact i4.const_mul _
  rw [hsplit, m0, m2, m4, ← g_I_neg_eq] at hmono
  have e : (1 : ℝ) / x ^ 1 - 1 / 2 * (((1 + 1) * 1 : ℕ) / x ^ 3) +
      1 / 8 * ((((3 + 1) * ((2 + 1) * ((1 + 1) * 1))) : ℕ) / x ^ 5) = 1 / x - 1 / x ^ 3 + 3 / x ^ 5 := by
    push_cast; field_simp; ring
  linarith [hmono, e]

lemma g_I_cs (z : ℝ) : Real.pi / 2 ≤ gI z * gI (-z) := by
  have ha := g_I_pos z
  have hb := g_I_pos (-z)
  set a := gI z with hadef
  set b := gI (-z) with hbdef
  set l := Real.sqrt (b / a) with hl
  have hl0 : 0 < l := Real.sqrt_pos.mpr (div_pos hb ha)
  have hl2 : l ^ 2 = b / a := Real.sq_sqrt (div_pos hb ha).le
  have hg : ∫ t in Ioi 0, Real.exp (-(1 / 2 : ℝ) * t ^ 2) = Real.sqrt (Real.pi / (1 / 2)) / 2 :=
    integral_gaussian_Ioi (1 / 2)
  have hgint : IntegrableOn (fun t : ℝ => Real.exp (-(1 / 2 : ℝ) * t ^ 2)) (Ioi 0) :=
    (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)).integrableOn
  have hint : IntegrableOn (fun t : ℝ => (l * Real.exp (z * t - t ^ 2 / 2) +
      l⁻¹ * Real.exp (-z * t - t ^ 2 / 2)) / 2) (Ioi 0) :=
    ((((g_exp_int z).integrableOn).const_mul l).add
      (((g_exp_int (-z)).integrableOn).const_mul l⁻¹)).div_const 2
  have hmono : ∫ t in Ioi 0, Real.exp (-(1 / 2 : ℝ) * t ^ 2) ≤
      ∫ t in Ioi 0, (l * Real.exp (z * t - t ^ 2 / 2) + l⁻¹ * Real.exp (-z * t - t ^ 2 / 2)) / 2 := by
    apply setIntegral_mono_on hgint hint measurableSet_Ioi
    intro t _
    have e1 : Real.exp (z * t - t ^ 2 / 2) = Real.exp (z * t) * Real.exp (-(1 / 2 : ℝ) * t ^ 2) := by
      rw [← Real.exp_add]; ring_nf
    have e2 : Real.exp (-z * t - t ^ 2 / 2) = (Real.exp (z * t))⁻¹ * Real.exp (-(1 / 2 : ℝ) * t ^ 2) := by
      rw [← Real.exp_neg, ← Real.exp_add]; ring_nf
    rw [e1, e2]
    set c := l * Real.exp (z * t) with hc
    have hc0 : 0 < c := mul_pos hl0 (Real.exp_pos _)
    have hE := Real.exp_pos (-(1 / 2 : ℝ) * t ^ 2)
    have key : l⁻¹ * ((Real.exp (z * t))⁻¹) = c⁻¹ := by rw [hc, mul_inv]
    have hamgm : 2 ≤ c + c⁻¹ := by
      have := sq_nonneg (c - 1)
      have : c + c⁻¹ - 2 = (c - 1) ^ 2 / c := by field_simp; ring
      have : 0 ≤ (c - 1) ^ 2 / c := div_nonneg (sq_nonneg _) hc0.le
      linarith
    have e3 : (l * (Real.exp (z * t) * Real.exp (-(1 / 2 : ℝ) * t ^ 2)) +
        l⁻¹ * ((Real.exp (z * t))⁻¹ * Real.exp (-(1 / 2 : ℝ) * t ^ 2))) / 2 =
        (c + c⁻¹) / 2 * Real.exp (-(1 / 2 : ℝ) * t ^ 2) := by
      rw [← key, hc]; ring
    rw [e3]
    nlinarith
  rw [integral_div, integral_add (((g_exp_int z).integrableOn).const_mul l)
    (((g_exp_int (-z)).integrableOn).const_mul l⁻¹), integral_const_mul, integral_const_mul, hg] at hmono
  have hIz : ∫ t in Ioi 0, Real.exp (z * t - t ^ 2 / 2) = a := rfl
  have hInz : ∫ t in Ioi 0, Real.exp (-z * t - t ^ 2 / 2) = b := rfl
  rw [hIz, hInz] at hmono
  -- l * a + l⁻¹ * b = 2 * sqrt (a b)
  have hlab : l * a = l⁻¹ * b := by
    have : l * l * a = b := by rw [← sq, hl2]; field_simp
    field_simp; linarith
  have hs : Real.sqrt (Real.pi / (1 / 2)) / 2 ≤ l * a := by linarith
  have hs2 : (Real.sqrt (Real.pi / (1 / 2)) / 2) ^ 2 = Real.pi / 2 := by
    rw [div_pow, Real.sq_sqrt (by positivity)]; ring
  have hla2 : (l * a) ^ 2 = a * b := by rw [mul_pow, hl2]; field_simp
  have h0 : 0 ≤ Real.sqrt (Real.pi / (1 / 2)) / 2 := by positivity
  nlinarith [mul_le_mul hs hs h0 (by positivity : 0 ≤ l * a)]

end LostSalesRQ

namespace LostSalesRQ

open MeasureTheory Set Real Filter Topology

noncomputable def gU (z : ℝ) : ℝ := stdNormalCdf z / stdNormalPdf z

lemma gU_eq (z : ℝ) : gU z = gI z := by
  unfold gU; rw [g_cdf_rep]; field_simp [(g_pdf_pos z).ne']

lemma gU_pos (z : ℝ) : 0 < gU z := by rw [gU_eq]; exact g_I_pos z

lemma gU_deriv (z : ℝ) : HasDerivAt gU (1 + z * gU z) z := by
  have h := (g_cdf_deriv z).div (g_pdf_deriv z) (g_pdf_pos z).ne'
  unfold gU
  refine h.congr_deriv ?_
  have := (g_pdf_pos z).ne'
  field_simp
  ring

lemma gU_cont : Continuous gU :=
  continuous_iff_continuousAt.mpr (fun z => (gU_deriv z).continuousAt)

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

lemma gU_strictMono : StrictMono gU := by
  apply strictMono_of_deriv_pos
  intro x
  rw [(gU_deriv x).deriv]
  exact g_one_add x

lemma gU_ge (z : ℝ) (hz : 0 ≤ z) : z < gU z := by
  have hmono : MonotoneOn (fun y => gU y - y) (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact (gU_cont.sub continuous_id).continuousOn
    · intro y _
      have hd : HasDerivAt (fun y => gU y - y) (1 + y * gU y - 1) y :=
        (gU_deriv y).sub (hasDerivAt_id' y)
      exact hd.differentiableAt.differentiableWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      have hy' : 0 < y := hy
      have hd : HasDerivAt (fun y => gU y - y) (1 + y * gU y - 1) y :=
        (gU_deriv y).sub (hasDerivAt_id' y)
      rw [hd.deriv]
      have := gU_pos y
      nlinarith
  have := hmono (mem_Ici.mpr le_rfl) (mem_Ici.mpr hz) hz
  simp only at this
  have h0 := gU_pos 0
  linarith

lemma gU_surj {s : ℝ} (hs : 0 < s) : ∃ z, gU z = s := by
  have h1 : gU (-(2 / s)) < s := by
    have hx : 0 < 2 / s := by positivity
    have h := g_I_neg_lt hx
    rw [gU_eq]
    have : 1 / (2 / s) = s / 2 := by field_simp
    rw [this] at h
    linarith
  have h2 : s < gU (s + 1) := by
    have := gU_ge (s + 1) (by linarith)
    linarith
  have hle : -(2 / s) ≤ s + 1 := by
    have : 0 < 2 / s := by positivity
    linarith
  obtain ⟨z, _, hz⟩ := intermediate_value_Icc hle gU_cont.continuousOn ⟨h1.le, h2.le⟩
  exact ⟨z, hz⟩

/-- The crossing lemma (positivity propagates from the right). -/
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

/-- The polynomial F(z,u) = 2 z u^3 - 8 u^2 + 13 z u + 13 (four times u^2 (S - 4)/2). -/
def gF (z u : ℝ) : ℝ := 2 * z * u ^ 3 - 8 * u ^ 2 + 13 * z * u + 13

lemma gF_cross {z u : ℝ} (hu : 0 < u) (hf : gF z u = 0) :
    0 < 6 * u ^ 3 * z ^ 2 + 2 * u ^ 3 - 10 * u ^ 2 * z + 13 * u * z ^ 2 - 3 * u + 13 * z := by
  unfold gF at hf
  have hP : 0 < 8 * (u ^ 2) ^ 3 + 316 * (u ^ 2) ^ 2 - 806 * u ^ 2 + 507 := by
    have hw : 0 ≤ u ^ 2 := sq_nonneg u
    nlinarith [sq_nonneg (u ^ 2 - 5/4), mul_nonneg hw (sq_nonneg (u ^ 2 - 5/4)),
      sq_nonneg (u ^ 2 - 6/5), mul_nonneg hw (sq_nonneg (u ^ 2 - 6/5))]
  have key : (6 * u ^ 3 * z ^ 2 + 2 * u ^ 3 - 10 * u ^ 2 * z + 13 * u * z ^ 2 - 3 * u + 13 * z) *
      (2 * u ^ 2 + 13) ^ 2 = u * (8 * (u ^ 2) ^ 3 + 316 * (u ^ 2) ^ 2 - 806 * u ^ 2 + 507) := by
    linear_combination (12 * u ^ 4 * z + 28 * u ^ 3 + 104 * u ^ 2 * z - 78 * u + 169 * z) * hf
  have h2 : 0 < (2 * u ^ 2 + 13) ^ 2 := by positivity
  have h3 : 0 < u * (8 * (u ^ 2) ^ 3 + 316 * (u ^ 2) ^ 2 - 806 * u ^ 2 + 507) := mul_pos hu hP
  rw [← key] at h3
  exact pos_of_mul_pos_left h3 h2.le

lemma g_N_pos {x : ℝ} (hx : 4 ≤ x) :
    0 < 3 * x ^ 12 - 17 * x ^ 10 - 80 * x ^ 8 + 86 * x ^ 6 - 144 * x ^ 4 + 54 * x ^ 2 - 54 := by
  have hw : 16 ≤ x ^ 2 := by nlinarith
  set w := x ^ 2 with hwdef
  have e : 3 * x ^ 12 - 17 * x ^ 10 - 80 * x ^ 8 + 86 * x ^ 6 - 144 * x ^ 4 + 54 * x ^ 2 - 54 =
      3 * w ^ 6 - 17 * w ^ 5 - 80 * w ^ 4 + 86 * w ^ 3 - 144 * w ^ 2 + 54 * w - 54 := by
    rw [hwdef]; ring
  rw [e]
  have h1 : 0 < w ^ 4 * (3 * w ^ 2 - 17 * w - 80) := by
    have : 0 < 3 * w ^ 2 - 17 * w - 80 := by nlinarith
    positivity
  have h2 : 0 < w ^ 2 * (86 * w - 144) + 54 * (w - 1) := by
    have : 0 < 86 * w - 144 := by linarith
    have : 0 < w ^ 2 := by positivity
    nlinarith
  nlinarith

lemma gF_far {z : ℝ} (hz : z ≤ -4) : 0 < gF z (gU z) := by
  set x := -z with hxdef
  have hx : 4 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hu0 := gU_pos z
  have hle : gU z ≤ 1 / x - 1 / x ^ 3 + 3 / x ^ 5 := by
    have h := g_I_neg_le hx0
    rw [hxdef, neg_neg, ← gU_eq] at h
    exact h
  set u := gU z
  set U := 1 / x - 1 / x ^ 3 + 3 / x ^ 5 with hU
  have hzx : z = -x := by rw [hxdef]; ring
  unfold gF
  rw [hzx]
  have h1 : u ^ 2 ≤ U ^ 2 := pow_le_pow_left₀ hu0.le hle 2
  have h2 : u ^ 3 ≤ U ^ 3 := pow_le_pow_left₀ hu0.le hle 3
  have hbase : 0 < 13 - 13 * x * U - 8 * U ^ 2 - 2 * x * U ^ 3 := by
    have e : (13 - 13 * x * U - 8 * U ^ 2 - 2 * x * U ^ 3) * x ^ 14 =
        3 * x ^ 12 - 17 * x ^ 10 - 80 * x ^ 8 + 86 * x ^ 6 - 144 * x ^ 4 + 54 * x ^ 2 - 54 := by
      rw [hU]; field_simp; ring
    have hN := g_N_pos hx
    rw [← e] at hN
    exact pos_of_mul_pos_left hN (by positivity)
  have i1 := mul_le_mul_of_nonneg_left hle (by linarith : (0 : ℝ) ≤ 13 * x)
  have i2 := mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ 2 * x)
  nlinarith

lemma gF_pos (z : ℝ) : 0 < gF z (gU z) := by
  -- apply the crossing lemma to t ↦ F(-t, u(-t))
  set g : ℝ → ℝ := fun t => gF (-t) (gU (-t)) with hg
  have hd : ∀ t, (-z) ≤ t → ∃ d, HasDerivAt g d t ∧ (g t = 0 → d < 0) := by
    intro t _
    have hu := (gU_deriv (-t)).comp t (hasDerivAt_neg t)
    have hz : HasDerivAt (fun t : ℝ => -t) (-1) t := hasDerivAt_neg t
    set u := gU (-t)
    have hG : HasDerivAt g (-(6 * u ^ 3 * (-t) ^ 2 + 2 * u ^ 3 - 10 * u ^ 2 * (-t) +
        13 * u * (-t) ^ 2 - 3 * u + 13 * (-t))) t := by
      have h := ((((hz.const_mul 2).mul (hu.pow 3)).sub ((hu.pow 2).const_mul 8)).add
        ((hz.const_mul 13).mul hu)).add_const 13
      refine h.congr_deriv ?_
      simp only [Function.comp, Pi.pow_apply, Nat.cast_ofNat]
      ring
    refine ⟨_, hG, fun h0 => ?_⟩
    have := gF_cross (gU_pos (-t)) h0
    linarith
  have hlarge : ∀ M, ∃ t, M ≤ t ∧ 0 < g t := by
    intro M
    refine ⟨max M 4, le_max_left _ _, ?_⟩
    exact gF_far (by have := le_max_right M 4; linarith)
  have := g2_crossing g (-z) hd hlarge (-z) le_rfl
  simpa [hg] using this

lemma g_tail_eq (z : ℝ) : 1 - stdNormalCdf z = stdNormalPdf z * gI (-z) := by
  have h := g_cdf_tail z
  rw [g_tail_rep] at h
  linarith

lemma g_K_pos (z : ℝ) :
    0 < 13 + 13 * z * gU z - 11 * gU z ^ 2 + 2 * z * gU z ^ 3 + 2 * gU z ^ 3 * gI (-z) := by
  have hF := gF_pos z
  unfold gF at hF
  have hcs := g_I_cs z
  rw [← gU_eq] at hcs
  have hu := gU_pos z
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have h1 : 3 / 2 < gU z * gI (-z) := by linarith
  have h2 : 0 < gU z ^ 2 * (2 * (gU z * gI (-z)) - 3) := by
    have : 0 < 2 * (gU z * gI (-z)) - 3 := by linarith
    positivity
  nlinarith

end LostSalesRQ

namespace LostSalesRQ

open MeasureTheory Set Real

lemma g_h_deriv (s z : ℝ) :
    HasDerivAt (fun z => stdNormalPdf z + z * stdNormalCdf z + s * (1 - stdNormalCdf z))
      (stdNormalCdf z - s * stdNormalPdf z) z := by
  have h := ((g_pdf_deriv z).add ((hasDerivAt_id' z).mul (g_cdf_deriv z))).add
    (((hasDerivAt_const z (1 : ℝ)).sub (g_cdf_deriv z)).const_mul s)
  refine h.congr_deriv ?_
  ring

end LostSalesRQ

open LostSalesRQ in
theorem solution (s : ℝ) (hs : 0 < s) :
    13 * s / (13 + 2 * s ^ 2) < gaussianRankProfile s := by
  obtain ⟨z0, hz0⟩ := gU_surj hs
  set h : ℝ → ℝ := fun z => stdNormalPdf z + z * stdNormalCdf z + s * (1 - stdNormalCdf z)
    with hhdef
  have hcont : Continuous h := by
    refine continuous_iff_continuousAt.mpr (fun z => (g_h_deriv s z).continuousAt)
  have hsign : ∀ y, stdNormalCdf y - s * stdNormalPdf y = stdNormalPdf y * (gU y - s) := by
    intro y
    unfold gU
    have := (g_pdf_pos y).ne'
    field_simp
  have hmin : ∀ z, h z0 ≤ h z := by
    intro z
    rcases le_total z z0 with hz | hz
    · have hanti : AntitoneOn h (Set.Iic z0) := by
        apply antitoneOn_of_deriv_nonpos (convex_Iic z0) hcont.continuousOn
        · intro y _; exact (g_h_deriv s y).differentiableAt.differentiableWithinAt
        · intro y hy
          rw [interior_Iic] at hy
          rw [(g_h_deriv s y).deriv, hsign]
          have h1 : gU y < gU z0 := gU_strictMono hy
          have := g_pdf_pos y
          nlinarith
      exact hanti (Set.mem_Iic.mpr hz) (Set.mem_Iic.mpr le_rfl) hz
    · have hmono : MonotoneOn h (Set.Ici z0) := by
        apply monotoneOn_of_deriv_nonneg (convex_Ici z0) hcont.continuousOn
        · intro y _; exact (g_h_deriv s y).differentiableAt.differentiableWithinAt
        · intro y hy
          rw [interior_Ici] at hy
          rw [(g_h_deriv s y).deriv, hsign]
          have h1 : gU z0 < gU y := gU_strictMono hy
          have := g_pdf_pos y
          nlinarith
      exact hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hz) hz
  have hG : h z0 ≤ gaussianRankProfile s := by
    unfold gaussianRankProfile
    exact le_ciInf hmin
  -- the value at the minimizer
  have hφ := g_pdf_pos z0
  have hΦ : stdNormalCdf z0 = stdNormalPdf z0 * s := by
    rw [← hz0]; unfold gU; field_simp
  have htail := g_tail_eq z0
  have hK := g_K_pos z0
  rw [hz0] at hK
  set φ0 := stdNormalPdf z0
  set v := gI (-z0)
  have hsum : φ0 * s + φ0 * v = 1 := by linarith
  have hval : h z0 = φ0 + z0 * (φ0 * s) + s * (φ0 * v) := by
    simp only [hhdef]; rw [htail, hΦ]
  have hpos : 0 < 13 + 2 * s ^ 2 := by positivity
  have hlt : 13 * s / (13 + 2 * s ^ 2) < h z0 := by
    rw [div_lt_iff₀ hpos, hval]
    have hφK := mul_pos hφ hK
    nlinarith [hsum]
  linarith

