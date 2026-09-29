-- Prove2me | solution 1 for LanglandsTunnell.ArchBessel.mellin_besselKernel_mul_besselKernel_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/57ffd439-3fc1-5ecb-a5c5-81989fa9c538

import Definitions.Def_LanglandsTunnell_ArchBessel
import Theorems.Thm_Complex_integrableOn_and_integral_Ioi_cpow_mul_one_add_cpow_neg_eq_Gamma_mul_Gamma_div
import Theorems.Thm_Complex_integrable_and_integral_prod_Ioi_exp_neg_add_mul_cpow_mul_cpow_mul_add_cpow_neg
import Theorems.Thm_LanglandsTunnell_ArchBessel_besselKernel_eq_cpow_mul_integral_exp_neg_sub_sq_div
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_ArchBessel_mellin_besselKernel_mul_besselKernel_eq

set_option autoImplicit false

p2m_open "MeasureTheory Set Real Complex LanglandsTunnell.ArchBessel P2MW.S_LanglandsTunnell_ArchBessel_mellin_besselKernel_mul_besselKernel_eq.LanglandsTunnell.ArchBessel"

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "ArchBessel.besselKernel_eq_cpow_mul_integral_exp_neg_sub_sq_div"
namespace ArchBessel
p2m_export "LanglandsTunnell.ArchBessel" "besselKernel besselKernel_eq_cpow_mul_integral_exp_neg_sub_sq_div"
namespace MellinKK
p2m_open "LanglandsTunnell.ArchBessel LanglandsTunnell"

theorem integrable_of_integral_ne_zero {α : Type*} [MeasurableSpace α] {μ : Measure α} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : α → E} (h : ∫ x, f x ∂μ ≠ 0) : Integrable f μ := by
  by_contra hf
  exact h (integral_undef hf)

theorem integrableOn_cpow_mul_exp_neg_mul {a : ℂ} {r : ℝ} (ha : 0 < a.re) (hr : 0 < r) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (a - 1) * Complex.exp (-((r : ℂ) * (t : ℂ)))) (Ioi 0) := by
  apply integrable_of_integral_ne_zero
  rw [Complex.integral_cpow_mul_exp_neg_mul_Ioi ha hr]
  exact mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl (by
    rw [one_div]; exact inv_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne')))) (Complex.Gamma_ne_zero_of_re_pos ha)

theorem integrableOn_rpow_mul_exp_neg_mul {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    IntegrableOn (fun t : ℝ => t ^ (a - 1) * Real.exp (-(r * t))) (Ioi 0) := by
  apply integrable_of_integral_ne_zero
  rw [Real.integral_rpow_mul_exp_neg_mul_Ioi ha hr]
  exact mul_ne_zero (by positivity) (Real.Gamma_pos_of_pos ha).ne'

theorem integral_cpow_mul_exp_neg_mul_sq {a : ℂ} {y : ℝ} (ha : 0 < a.re) (hy : 0 < y) :
    ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (2 * a - 1) * Complex.exp (-((y : ℂ) * (t : ℂ) ^ 2)) =
      (1 / 2 : ℂ) * ((1 / (y : ℂ)) ^ a * Complex.Gamma a) := by
  have hsub := integral_comp_rpow_Ioi
    (fun u : ℝ => (u : ℂ) ^ (a - 1) * Complex.exp (-((y : ℂ) * (u : ℂ)))) (p := 2) two_ne_zero
  rw [Complex.integral_cpow_mul_exp_neg_mul_Ioi ha hy] at hsub
  have hcongr : ∫ x in Ioi (0 : ℝ), (|(2 : ℝ)| * x ^ ((2 : ℝ) - 1)) •
        ((((x ^ (2 : ℝ)) : ℝ) : ℂ) ^ (a - 1) * Complex.exp (-((y : ℂ) * (((x ^ (2 : ℝ)) : ℝ) : ℂ)))) =
      ∫ x in Ioi (0 : ℝ), (2 : ℂ) * ((x : ℂ) ^ (2 * a - 1) * Complex.exp (-((y : ℂ) * (x : ℂ) ^ 2))) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    have hx : 0 < x := hx
    have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
    have e1 : ((((x ^ (2 : ℝ)) : ℝ) : ℂ)) ^ (a - 1) = (x : ℂ) ^ ((2 : ℂ) * (a - 1)) := by
      rw [← Complex.cpow_mul_ofReal_nonneg hx.le]; push_cast; ring_nf
    have e2 : ((((x ^ (2 : ℝ)) : ℝ) : ℂ)) = (x : ℂ) ^ 2 := by
      rw [Real.rpow_two]; push_cast; ring
    have e3 : |(2 : ℝ)| * x ^ ((2 : ℝ) - 1) = 2 * x := by norm_num
    rw [e3, e1, e2, Complex.real_smul]
    push_cast
    have e4 : (x : ℂ) * (x : ℂ) ^ ((2 : ℂ) * (a - 1)) = (x : ℂ) ^ (2 * a - 1) := by
      rw [show (x : ℂ) * (x : ℂ) ^ ((2 : ℂ) * (a - 1)) = (x : ℂ) ^ (1 : ℂ) * (x : ℂ) ^ ((2 : ℂ) * (a - 1)) by
        rw [Complex.cpow_one], ← Complex.cpow_add _ _ hx0]
      congr 1; ring
    calc (2 : ℂ) * (x : ℂ) * ((x : ℂ) ^ ((2 : ℂ) * (a - 1)) * Complex.exp (-((y : ℂ) * (x : ℂ) ^ 2)))
        = 2 * (((x : ℂ) * (x : ℂ) ^ ((2 : ℂ) * (a - 1))) * Complex.exp (-((y : ℂ) * (x : ℂ) ^ 2))) := by ring
      _ = _ := by rw [e4]
  rw [hcongr, integral_const_mul] at hsub
  have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
  calc ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (2 * a - 1) * Complex.exp (-((y : ℂ) * (t : ℂ) ^ 2))
      = (1 / 2 : ℂ) * ((2 : ℂ) * ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (2 * a - 1) * Complex.exp (-((y : ℂ) * (t : ℂ) ^ 2))) := by
        field_simp
    _ = (1 / 2 : ℂ) * ((1 / (y : ℂ)) ^ a * Complex.Gamma a) := by rw [hsub]

theorem integral_rpow_mul_exp_neg_mul_sq {a y : ℝ} (ha : 0 < a) (hy : 0 < y) :
    ∫ t in Ioi (0 : ℝ), t ^ (2 * a - 1) * Real.exp (-(y * t ^ 2)) = (1 / 2) * ((1 / y) ^ a * Real.Gamma a) := by
  have hsub := integral_comp_rpow_Ioi
    (fun u : ℝ => u ^ (a - 1) * Real.exp (-(y * u))) (p := 2) two_ne_zero
  rw [Real.integral_rpow_mul_exp_neg_mul_Ioi ha hy] at hsub
  have hcongr : ∫ x in Ioi (0 : ℝ), (|(2 : ℝ)| * x ^ ((2 : ℝ) - 1)) •
        ((x ^ (2 : ℝ)) ^ (a - 1) * Real.exp (-(y * x ^ (2 : ℝ)))) =
      ∫ x in Ioi (0 : ℝ), 2 * (x ^ (2 * a - 1) * Real.exp (-(y * x ^ 2))) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    have hx : 0 < x := hx
    have e1 : (x ^ (2 : ℝ)) ^ (a - 1) = x ^ (2 * (a - 1)) := by rw [← Real.rpow_mul hx.le]
    have e2 : x ^ (2 : ℝ) = x ^ 2 := Real.rpow_two x
    have e3 : |(2 : ℝ)| * x ^ ((2 : ℝ) - 1) = 2 * x := by norm_num
    rw [e3, e1, e2, smul_eq_mul]
    have e4 : x * x ^ (2 * (a - 1)) = x ^ (2 * a - 1) := by
      rw [show x * x ^ (2 * (a - 1)) = x ^ (1 : ℝ) * x ^ (2 * (a - 1)) by rw [Real.rpow_one],
        ← Real.rpow_add hx]
      congr 1; ring
    calc 2 * x * (x ^ (2 * (a - 1)) * Real.exp (-(y * x ^ 2)))
        = 2 * ((x * x ^ (2 * (a - 1))) * Real.exp (-(y * x ^ 2))) := by ring
      _ = _ := by rw [e4]
  rw [hcongr, integral_const_mul] at hsub
  linarith

theorem integrableOn_rpow_mul_exp_neg_mul_sq {a y : ℝ} (ha : 0 < a) (hy : 0 < y) :
    IntegrableOn (fun t : ℝ => t ^ (2 * a - 1) * Real.exp (-(y * t ^ 2))) (Ioi 0) := by
  apply integrable_of_integral_ne_zero
  rw [integral_rpow_mul_exp_neg_mul_sq ha hy]
  exact mul_ne_zero (by norm_num) (mul_ne_zero (by positivity) (Real.Gamma_pos_of_pos ha).ne')

theorem integrableOn_rpow_mul_one_add_sq_rpow_neg {p σ : ℝ} (hp : -1 < p) (hσ : 0 < σ) (hpσ : p - 2 * σ < -1) :
    IntegrableOn (fun t : ℝ => t ^ p * (1 + t ^ 2) ^ (-σ)) (Ioi 0) := by
  have hmeas : Measurable (fun t : ℝ => t ^ p * (1 + t ^ 2) ^ (-σ)) :=
    (measurable_id.pow_const p).mul ((measurable_const.add (measurable_id.pow_const 2)).pow_const _)
  have hnn : ∀ t : ℝ, 0 < t → 0 ≤ t ^ p * (1 + t ^ 2) ^ (-σ) := fun t ht =>
    mul_nonneg (Real.rpow_nonneg ht.le _) (Real.rpow_nonneg (by positivity) _)
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one, integrableOn_union]
  constructor
  ·
    have h1 : IntegrableOn (fun t : ℝ => t ^ p) (Ioc 0 1) := (intervalIntegral.intervalIntegrable_rpow' hp).1
    refine h1.mono' hmeas.aestronglyMeasurable ?_
    refine (ae_restrict_mem measurableSet_Ioc).mono (fun t ht => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hnn t ht.1)]
    have : (1 + t ^ 2) ^ (-σ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith) (by linarith)
    calc t ^ p * (1 + t ^ 2) ^ (-σ) ≤ t ^ p * 1 :=
          mul_le_mul_of_nonneg_left this (Real.rpow_nonneg ht.1.le _)
      _ = t ^ p := mul_one _
  ·
    have h1 : IntegrableOn (fun t : ℝ => t ^ (p - 2 * σ)) (Ioi 1) := integrableOn_Ioi_rpow_of_lt hpσ one_pos
    refine h1.mono' hmeas.aestronglyMeasurable ?_
    refine (ae_restrict_mem measurableSet_Ioi).mono (fun t ht => ?_)
    have ht : 1 < t := ht
    have ht0 : 0 < t := by linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (hnn t ht0)]
    have hle : (1 + t ^ 2) ^ (-σ) ≤ (t ^ 2) ^ (-σ) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
    have e : (t ^ 2) ^ (-σ) = t ^ (-(2 * σ)) := by
      rw [← Real.rpow_natCast t 2, ← Real.rpow_mul ht0.le]; push_cast; ring_nf
    calc t ^ p * (1 + t ^ 2) ^ (-σ) ≤ t ^ p * (t ^ 2) ^ (-σ) :=
          mul_le_mul_of_nonneg_left hle (Real.rpow_nonneg ht0.le _)
      _ = t ^ (p - 2 * σ) := by rw [e, ← Real.rpow_add ht0]; ring_nf

def crate (p : ℝ × ℝ) : ℝ := (p.1 + p.2) / (4 * (p.1 * p.2))

theorem crate_pos {p : ℝ × ℝ} (h1 : 0 < p.1) (h2 : 0 < p.2) : 0 < crate p := by
  unfold crate; positivity

def amp (μ ν : ℂ) (p : ℝ × ℝ) : ℂ :=
  (2 : ℂ) ^ (μ + ν) * (Complex.exp (-(((p.1 + p.2 : ℝ)) : ℂ)) * (p.1 : ℂ) ^ (μ - 1) * (p.2 : ℂ) ^ (ν - 1))

def H (μ ν s : ℂ) (q : ℝ × (ℝ × ℝ)) : ℂ :=
  amp μ ν q.2 * ((q.1 : ℂ) ^ (2 * ((s - μ - ν) / 2) - 1) * Complex.exp (-(((crate q.2 : ℝ) : ℂ) * (q.1 : ℂ) ^ 2)))

theorem measurable_amp (μ ν : ℂ) : Measurable (amp μ ν) := by
  unfold amp
  exact measurable_const.mul ((((Complex.measurable_ofReal.comp (measurable_fst.add measurable_snd)).neg.cexp).mul
    ((Complex.measurable_ofReal.comp measurable_fst).pow_const _)).mul
    ((Complex.measurable_ofReal.comp measurable_snd).pow_const _))

theorem measurable_crate : Measurable crate := by
  unfold crate
  exact (measurable_fst.add measurable_snd).div (measurable_const.mul (measurable_fst.mul measurable_snd))

theorem measurable_H (μ ν s : ℂ) : Measurable (H μ ν s) := by
  unfold H
  exact ((measurable_amp μ ν).comp measurable_snd).mul
    (((Complex.measurable_ofReal.comp measurable_fst).pow_const _).mul
      (((Complex.measurable_ofReal.comp (measurable_crate.comp measurable_snd)).mul
        ((Complex.measurable_ofReal.comp measurable_fst).pow_const _)).neg.cexp))

theorem H_eq (μ ν s : ℂ) {x τ σ : ℝ} (hx : 0 < x) (hτ : 0 < τ) (hσ : 0 < σ) :
    (x : ℂ) ^ (s - 1) * ((((2 / x : ℝ)) : ℂ) ^ μ * (((2 / x : ℝ)) : ℂ) ^ ν) *
      (((Real.exp (-(τ + x ^ 2 / (4 * τ))) : ℂ) * (τ : ℂ) ^ (μ - 1)) *
        ((Real.exp (-(σ + x ^ 2 / (4 * σ))) : ℂ) * (σ : ℂ) ^ (ν - 1))) = H μ ν s (x, (τ, σ)) := by
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have harg : (x : ℂ).arg ≠ Real.pi := by rw [Complex.arg_ofReal_of_nonneg hx.le]; exact Real.pi_ne_zero.symm
  simp only [H, amp, crate]

  have e2x : ∀ w : ℂ, (((2 / x : ℝ)) : ℂ) ^ w = (2 : ℂ) ^ w * (x : ℂ) ^ (-w) := by
    intro w
    rw [show (((2 / x : ℝ)) : ℂ) = (((2 : ℝ)) : ℂ) * (((x⁻¹ : ℝ)) : ℂ) by push_cast; ring,
      Complex.mul_cpow_ofReal_nonneg (by norm_num) (by positivity), Complex.ofReal_inv,
      Complex.inv_cpow _ _ harg, ← Complex.cpow_neg]
    push_cast; ring

  have eexp : (Real.exp (-(τ + x ^ 2 / (4 * τ))) : ℂ) * (Real.exp (-(σ + x ^ 2 / (4 * σ))) : ℂ) =
      Complex.exp (-(((τ + σ : ℝ)) : ℂ)) * Complex.exp (-((((τ + σ) / (4 * (τ * σ)) : ℝ) : ℂ) * (x : ℂ) ^ 2)) := by
    rw [Complex.ofReal_exp, Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    have : -(τ + x ^ 2 / (4 * τ)) + -(σ + x ^ 2 / (4 * σ)) = -(τ + σ) + -((τ + σ) / (4 * (τ * σ)) * x ^ 2) := by
      field_simp; ring
    have := congrArg (fun r : ℝ => (r : ℂ)) this
    push_cast at this ⊢
    linear_combination this

  have ex : (x : ℂ) ^ (s - 1) * ((x : ℂ) ^ (-μ) * (x : ℂ) ^ (-ν)) = (x : ℂ) ^ (2 * ((s - μ - ν) / 2) - 1) := by
    rw [← Complex.cpow_add _ _ hx0, ← Complex.cpow_add _ _ hx0]; congr 1; ring
  rw [e2x μ, e2x ν]
  calc _ = ((2 : ℂ) ^ μ * (2 : ℂ) ^ ν) * ((τ : ℂ) ^ (μ - 1) * (σ : ℂ) ^ (ν - 1)) *
        (((x : ℂ) ^ (s - 1) * ((x : ℂ) ^ (-μ) * (x : ℂ) ^ (-ν))) *
          ((Real.exp (-(τ + x ^ 2 / (4 * τ))) : ℂ) * (Real.exp (-(σ + x ^ 2 / (4 * σ))) : ℂ))) := by ring
    _ = ((2 : ℂ) ^ μ * (2 : ℂ) ^ ν) * ((τ : ℂ) ^ (μ - 1) * (σ : ℂ) ^ (ν - 1)) *
        ((x : ℂ) ^ (2 * ((s - μ - ν) / 2) - 1) *
          (Complex.exp (-(((τ + σ : ℝ)) : ℂ)) * Complex.exp (-((((τ + σ) / (4 * (τ * σ)) : ℝ) : ℂ) * (x : ℂ) ^ 2)))) := by
        rw [ex, eexp]
    _ = _ := by rw [← Complex.cpow_add _ _ two_ne_zero]; ring

theorem norm_amp (μ ν : ℂ) {τ σ : ℝ} (hτ : 0 < τ) (hσ : 0 < σ) :
    ‖amp μ ν (τ, σ)‖ = (2 : ℝ) ^ (μ + ν).re * (Real.exp (-(τ + σ)) * τ ^ (μ.re - 1) * σ ^ (ν.re - 1)) := by
  simp only [amp, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hτ, Complex.norm_cpow_eq_rpow_re_of_pos hσ,
    Complex.norm_exp, Complex.neg_re, Complex.ofReal_re, Complex.sub_re, Complex.one_re]
  congr 1
  rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.norm_cpow_eq_rpow_re_of_pos two_pos]

theorem norm_H (μ ν s : ℂ) {x τ σ : ℝ} (hx : 0 < x) (hτ : 0 < τ) (hσ : 0 < σ) :
    ‖H μ ν s (x, (τ, σ))‖ = ‖amp μ ν (τ, σ)‖ *
      (x ^ (2 * ((s.re - μ.re - ν.re) / 2) - 1) * Real.exp (-(crate (τ, σ) * x ^ 2))) := by
  rw [H, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.norm_exp]
  congr 2
  · congr 1
    simp
    try ring
  · congr 1
    rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, ← Complex.ofReal_neg, Complex.ofReal_re]

theorem integrable_H (μ ν s : ℂ) (hs : |μ.re| + |ν.re| < s.re) :
    Integrable (H μ ν s) ((volume.restrict (Ioi (0:ℝ))).prod
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ))))) := by
  have hμ1 := le_abs_self μ.re; have hμ2 := neg_abs_le μ.re
  have hν1 := le_abs_self ν.re; have hν2 := neg_abs_le ν.re
  have hw : 0 < (s.re - μ.re - ν.re) / 2 := by linarith

  have hα : 0 < ((((s + μ - ν) / 2 : ℂ))).re := by simp; linarith
  have hβ : 0 < ((((s - μ + ν) / 2 : ℂ))).re := by simp; linarith
  have hγ : 0 < ((s + μ - ν) / 2 + (s - μ + ν) / 2 - (s - μ - ν) / 2 : ℂ).re := by simp; linarith
  rw [integrable_prod_iff' (measurable_H μ ν s).aestronglyMeasurable]
  constructor
  · rw [Measure.prod_restrict]
    refine (ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)).mono (fun p hp => ?_)
    obtain ⟨hτ, hσ⟩ := hp
    have hτ : 0 < p.1 := hτ; have hσ : 0 < p.2 := hσ
    have hc := crate_pos hτ hσ
    have h1 := (integrableOn_rpow_mul_exp_neg_mul_sq hw hc).const_mul ‖amp μ ν (p.1, p.2)‖
    refine h1.mono' ((measurable_H μ ν s).comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable ?_
    refine (ae_restrict_mem measurableSet_Ioi).mono (fun x hx => ?_)
    have hx : 0 < x := hx
    rw [show p = (p.1, p.2) from rfl, norm_H μ ν s hx hτ hσ]
  ·
    have hD := (Complex.integrable_and_integral_prod_Ioi_exp_neg_add_mul_cpow_mul_cpow_mul_add_cpow_neg
      (((s.re + μ.re - ν.re) / 2 : ℝ) : ℂ) (((s.re - μ.re + ν.re) / 2 : ℝ) : ℂ) (((s.re - μ.re - ν.re) / 2 : ℝ) : ℂ)
      (by simp; linarith) (by simp; linarith) (by push_cast; simp; linarith)).1
    have hDn := hD.norm.const_mul ((2 : ℝ) ^ (μ + ν).re * (1 / 2 * ((4 : ℝ) ^ ((s.re - μ.re - ν.re) / 2) *
      Real.Gamma ((s.re - μ.re - ν.re) / 2))))
    refine hDn.congr ?_
    rw [Measure.prod_restrict]
    refine (ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)).mono (fun p hp => ?_)
    obtain ⟨hτ, hσ⟩ := hp
    have hτ : 0 < p.1 := hτ; have hσ : 0 < p.2 := hσ
    have hc := crate_pos hτ hσ
    have hts : 0 < p.1 + p.2 := by positivity
    rw [show p = (p.1, p.2) from rfl]
    beta_reduce
    rw [setIntegral_congr_fun measurableSet_Ioi (fun x (hx : x ∈ Ioi (0:ℝ)) => norm_H μ ν s (mem_Ioi.mp hx) hτ hσ),
      integral_const_mul,
      integral_rpow_mul_exp_neg_mul_sq hw hc, norm_amp μ ν hτ hσ]
    simp only [norm_mul, Complex.norm_exp, Complex.norm_cpow_eq_rpow_re_of_pos hτ,
      Complex.norm_cpow_eq_rpow_re_of_pos hσ, Complex.norm_cpow_eq_rpow_re_of_pos hts,
      Complex.neg_re, Complex.ofReal_re, Complex.sub_re, Complex.one_re]

    have ec : (1 / crate (p.1, p.2)) ^ ((s.re - μ.re - ν.re) / 2) =
        (4 : ℝ) ^ ((s.re - μ.re - ν.re) / 2) * (p.1 ^ ((s.re - μ.re - ν.re) / 2) * p.2 ^ ((s.re - μ.re - ν.re) / 2) *
          (p.1 + p.2) ^ (-((s.re - μ.re - ν.re) / 2))) := by
      unfold crate
      rw [show 1 / ((p.1 + p.2) / (4 * (p.1 * p.2))) = 4 * (p.1 * p.2 * (p.1 + p.2)⁻¹) by field_simp,
        Real.mul_rpow (by norm_num) (by positivity), Real.mul_rpow (by positivity) (by positivity),
        Real.mul_rpow hτ.le hσ.le, Real.inv_rpow hts.le, ← Real.rpow_neg hts.le]
    rw [ec]
    have e1 : p.1 ^ (μ.re - 1) * p.1 ^ ((s.re - μ.re - ν.re) / 2) = p.1 ^ ((s.re + μ.re - ν.re) / 2 - 1) := by
      rw [← Real.rpow_add hτ]; congr 1; ring
    have e2 : p.2 ^ (ν.re - 1) * p.2 ^ ((s.re - μ.re - ν.re) / 2) = p.2 ^ ((s.re - μ.re + ν.re) / 2 - 1) := by
      rw [← Real.rpow_add hσ]; congr 1; ring
    rw [← e1, ← e2]
    ring

end LanglandsTunnell.ArchBessel.MellinKK

end

open LanglandsTunnell.ArchBessel.MellinKK in
theorem solution (μ ν s : ℂ) (hs : |μ.re| + |ν.re| < s.re) :
    MellinConvergent (fun x : ℝ => besselKernel μ x * besselKernel ν x) s ∧
      mellin (fun x : ℝ => besselKernel μ x * besselKernel ν x) s =
        (2 : ℂ) ^ (s - 1) *
          (Complex.Gamma ((s + μ + ν) / 2) * Complex.Gamma ((s + μ - ν) / 2) *
            Complex.Gamma ((s - μ + ν) / 2) * Complex.Gamma ((s - μ - ν) / 2)) / Complex.Gamma s := by
  have hμ1 := le_abs_self μ.re; have hμ2 := neg_abs_le μ.re
  have hν1 := le_abs_self ν.re; have hν2 := neg_abs_le ν.re
  have h20 : (2 : ℂ) ≠ 0 := two_ne_zero

  set α : ℂ := (s + μ - ν) / 2 with hαd
  set β : ℂ := (s - μ + ν) / 2 with hβd
  set γ : ℂ := (s - μ - ν) / 2 with hγd
  have hα : 0 < α.re := by simp [hαd]; linarith
  have hβ : 0 < β.re := by simp [hβd]; linarith
  have hγ : 0 < γ.re := by simp [hγd]; linarith
  have hαβγ : 0 < (α + β - γ).re := by simp [hαd, hβd, hγd]; linarith
  have hH := integrable_H μ ν s hs

  have hpt : ∀ x : ℝ, 0 < x → (x : ℂ) ^ (s - 1) • (besselKernel μ x * besselKernel ν x) =
      ∫ p : ℝ × ℝ, H μ ν s (x, p) ∂((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) := by
    intro x hx
    rw [LanglandsTunnell.ArchBessel.besselKernel_eq_cpow_mul_integral_exp_neg_sub_sq_div μ x hx,
      LanglandsTunnell.ArchBessel.besselKernel_eq_cpow_mul_integral_exp_neg_sub_sq_div ν x hx, smul_eq_mul,
      show ∀ (a b c d e : ℂ), e * (a * b * (c * d)) = (e * (a * c)) * (b * d) from fun a b c d e => by ring,
      ← integral_prod_mul, ← integral_const_mul, Measure.prod_restrict]
    refine setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioi) (fun p hp => ?_)
    obtain ⟨hτ, hσ⟩ := hp
    rw [show p = (p.1, p.2) from rfl]
    exact H_eq μ ν s hx hτ hσ
  refine ⟨?_, ?_⟩
  ·
    have h1 := hH.integral_prod_left
    exact IntegrableOn.congr_fun h1 (fun x hx => (hpt x hx).symm) measurableSet_Ioi
  ·
    unfold mellin
    rw [setIntegral_congr_fun measurableSet_Ioi (fun x hx => hpt x hx),
      integral_integral_swap (f := fun x p => H μ ν s (x, p)) hH]

    have hinner : ∫ p : ℝ × ℝ, (∫ x in Ioi (0:ℝ), H μ ν s (x, p)) ∂((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) =
        ∫ p : ℝ × ℝ, ((2 : ℂ) ^ (μ + ν) * ((1 / 2 : ℂ) * Complex.Gamma γ * (4 : ℂ) ^ γ)) *
          (Complex.exp (-(((p.1 + p.2 : ℝ)) : ℂ)) * (p.1 : ℂ) ^ (α - 1) * (p.2 : ℂ) ^ (β - 1) *
            (((p.1 + p.2 : ℝ)) : ℂ) ^ (-γ)) ∂((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) := by
      rw [Measure.prod_restrict]
      refine setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioi) (fun p hp => ?_)
      obtain ⟨hτ, hσ⟩ := hp
      have hτ : 0 < p.1 := hτ; have hσ : 0 < p.2 := hσ
      have hτ0 : (p.1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hτ.ne'
      have hσ0 : (p.2 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hσ.ne'
      have hts : 0 < p.1 + p.2 := by positivity
      have hc := crate_pos hτ hσ
      rw [show (fun x : ℝ => H μ ν s (x, p)) = fun x : ℝ => amp μ ν p *
          ((x : ℂ) ^ (2 * ((s - μ - ν) / 2) - 1) * Complex.exp (-(((crate p : ℝ) : ℂ) * (x : ℂ) ^ 2))) from rfl,
        integral_const_mul, integral_cpow_mul_exp_neg_mul_sq (by rw [← hγd]; exact hγ) hc]
      rw [show p = (p.1, p.2) from rfl]
      simp only [amp, crate, ← hγd]

      have ec : ((1 : ℂ) / (((p.1 + p.2) / (4 * (p.1 * p.2)) : ℝ) : ℂ)) ^ γ =
          (4 : ℂ) ^ γ * ((p.1 : ℂ) ^ γ * (p.2 : ℂ) ^ γ * (((p.1 + p.2 : ℝ)) : ℂ) ^ (-γ)) := by
        have e0 : (1 : ℂ) / (((p.1 + p.2) / (4 * (p.1 * p.2)) : ℝ) : ℂ) =
            (((4 : ℝ)) : ℂ) * ((((p.1 * p.2) * (p.1 + p.2)⁻¹ : ℝ)) : ℂ) := by
          have : (1 : ℝ) / ((p.1 + p.2) / (4 * (p.1 * p.2))) = 4 * ((p.1 * p.2) * (p.1 + p.2)⁻¹) := by field_simp
          rw [← Complex.ofReal_mul, ← this]; push_cast; ring
        rw [e0, Complex.mul_cpow_ofReal_nonneg (by norm_num) (by positivity), Complex.ofReal_mul,
          Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity), Complex.ofReal_mul,
          Complex.mul_cpow_ofReal_nonneg hτ.le hσ.le, Complex.ofReal_inv,
          Complex.inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg hts.le]; exact Real.pi_ne_zero.symm),
          ← Complex.cpow_neg]
        push_cast; ring
      rw [ec]
      have e1 : (p.1 : ℂ) ^ (μ - 1) * (p.1 : ℂ) ^ γ = (p.1 : ℂ) ^ (α - 1) := by
        rw [← Complex.cpow_add _ _ hτ0]; congr 1; rw [hαd, hγd]; ring
      have e2 : (p.2 : ℂ) ^ (ν - 1) * (p.2 : ℂ) ^ γ = (p.2 : ℂ) ^ (β - 1) := by
        rw [← Complex.cpow_add _ _ hσ0]; congr 1; rw [hβd, hγd]; ring
      rw [← e1, ← e2]
      push_cast
      ring
    rw [hinner, integral_const_mul,
      (Complex.integrable_and_integral_prod_Ioi_exp_neg_add_mul_cpow_mul_cpow_mul_add_cpow_neg α β γ hα hβ hαβγ).2]

    have hs1 : α + β - γ = (s + μ + ν) / 2 := by rw [hαd, hβd, hγd]; ring
    have hs2 : α + β = s := by rw [hαd, hβd]; ring
    rw [hs1, hs2]
    have e4 : (4 : ℂ) ^ γ = (2 : ℂ) ^ γ * (2 : ℂ) ^ γ := by
      rw [show (4 : ℂ) = ((2 : ℝ) : ℂ) * ((2 : ℝ) : ℂ) by norm_num,
        Complex.mul_cpow_ofReal_nonneg (by norm_num) (by norm_num)]
      push_cast; ring
    have e5 : (2 : ℂ) ^ (μ + ν) * ((2 : ℂ) ^ γ * (2 : ℂ) ^ γ) * (1 / 2) = (2 : ℂ) ^ (s - 1) := by
      rw [← Complex.cpow_add _ _ h20, ← Complex.cpow_add _ _ h20,
        show μ + ν + (γ + γ) = s by rw [hγd]; ring, Complex.cpow_sub _ _ h20, Complex.cpow_one]
      ring
    rw [e4]
    calc (2 : ℂ) ^ (μ + ν) * (1 / 2 * Complex.Gamma γ * ((2 : ℂ) ^ γ * (2 : ℂ) ^ γ)) *
          (Complex.Gamma ((s + μ + ν) / 2) * Complex.Gamma α * Complex.Gamma β / Complex.Gamma s)
        = ((2 : ℂ) ^ (μ + ν) * ((2 : ℂ) ^ γ * (2 : ℂ) ^ γ) * (1 / 2)) *
          (Complex.Gamma ((s + μ + ν) / 2) * Complex.Gamma α * Complex.Gamma β * Complex.Gamma γ) / Complex.Gamma s := by
          ring
      _ = _ := by rw [e5, hαd, hβd, hγd]

#print axioms solution

end S_LanglandsTunnell_ArchBessel_mellin_besselKernel_mul_besselKernel_eq
end P2MW
export P2MW.S_LanglandsTunnell_ArchBessel_mellin_besselKernel_mul_besselKernel_eq (solution)
