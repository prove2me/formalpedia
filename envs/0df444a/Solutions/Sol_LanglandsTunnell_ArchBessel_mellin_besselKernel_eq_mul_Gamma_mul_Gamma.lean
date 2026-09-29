-- Prove2me | solution 1 for LanglandsTunnell.ArchBessel.mellin_besselKernel_eq_mul_Gamma_mul_Gamma
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/bd585d1b-7b8f-55d1-9a77-4e725519683a

import Definitions.Def_LanglandsTunnell_ArchBessel
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_ArchBessel_mellin_besselKernel_eq_mul_Gamma_mul_Gamma

set_option autoImplicit false

p2m_open "MeasureTheory Set Real Complex LanglandsTunnell.ArchBessel P2MW.S_LanglandsTunnell_ArchBessel_mellin_besselKernel_eq_mul_Gamma_mul_Gamma.LanglandsTunnell.ArchBessel"

noncomputable section

namespace LanglandsTunnell
namespace ArchBessel
p2m_export "LanglandsTunnell.ArchBessel" "besselKernel"
namespace MellinK
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

theorem integrableOn_rpow_mul_exp_neg_mul_add_inv {c : ℝ} (hc : 0 < c) (n : ℝ) :
    IntegrableOn (fun t : ℝ => t ^ (n - 1) * Real.exp (-(c * (t + t⁻¹)))) (Ioi 0) := by
  obtain ⟨k, hk⟩ := exists_nat_gt (-n)
  have hnk : 0 < n + k := by linarith
  have hI := (integrableOn_rpow_mul_exp_neg_mul hnk hc).const_mul ((k.factorial : ℝ) / c ^ k)
  have hmeas : Measurable (fun t : ℝ => t ^ (n - 1) * Real.exp (-(c * (t + t⁻¹)))) :=
    (measurable_id.pow_const _).mul (Real.measurable_exp.comp ((measurable_const.mul
      (measurable_id.add measurable_inv)).neg))
  refine hI.mono' hmeas.aestronglyMeasurable ?_
  refine (ae_restrict_mem measurableSet_Ioi).mono (fun t ht => ?_)
  have ht : 0 < t := ht
  have hct : 0 < c / t := div_pos hc ht

  have hexp : Real.exp (-(c * t⁻¹)) ≤ (k.factorial : ℝ) / c ^ k * t ^ (k : ℝ) := by
    have h1 := Real.pow_div_factorial_le_exp (c / t) hct.le k
    have hfac : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
    have hpos : 0 < (c / t) ^ k / k.factorial := by positivity
    rw [show -(c * t⁻¹) = -(c / t) by ring, Real.exp_neg]
    calc (Real.exp (c / t))⁻¹ ≤ ((c / t) ^ k / k.factorial)⁻¹ := inv_anti₀ hpos h1
      _ = (k.factorial : ℝ) / c ^ k * t ^ (k : ℝ) := by
          rw [Real.rpow_natCast, div_pow]; field_simp
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_pos _).le)]
  have esplit : Real.exp (-(c * (t + t⁻¹))) = Real.exp (-(c * t)) * Real.exp (-(c * t⁻¹)) := by
    rw [← Real.exp_add]; ring_nf
  rw [esplit]
  calc t ^ (n - 1) * (Real.exp (-(c * t)) * Real.exp (-(c * t⁻¹)))
      ≤ t ^ (n - 1) * (Real.exp (-(c * t)) * ((k.factorial : ℝ) / c ^ k * t ^ (k : ℝ))) := by
        gcongr
    _ = (k.factorial : ℝ) / c ^ k * (t ^ (n + k - 1) * Real.exp (-(c * t))) := by
        rw [show n + (k : ℝ) - 1 = (n - 1) + k by ring, Real.rpow_add ht]; ring

theorem norm_besselIntegrand (ν : ℂ) (x t : ℝ) (ht : 0 < t) :
    ‖(Real.exp (-(x * (t + t⁻¹) / 2)) : ℂ) * ((t : ℂ) ^ (ν - 1))‖ =
      t ^ (ν.re - 1) * Real.exp (-(x / 2 * (t + t⁻¹))) := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.sub_re, Complex.one_re, mul_comm]
  congr 1; ring_nf

theorem continuousAt_besselKernel (ν : ℂ) {x₀ : ℝ} (hx₀ : 0 < x₀) :
    ContinuousAt (fun x : ℝ => besselKernel ν x) x₀ := by
  unfold besselKernel
  have hmeasF : ∀ x : ℝ, Measurable (fun t : ℝ => (Real.exp (-(x * (t + t⁻¹) / 2)) : ℂ) * ((t : ℂ) ^ (ν - 1))) :=
    fun x => (Complex.measurable_ofReal.comp (Real.measurable_exp.comp
      (((measurable_const.mul (measurable_id.add measurable_inv)).div_const 2).neg))).mul
      ((Complex.measurable_ofReal.comp measurable_id).pow_const _)
  refine continuousAt_of_dominated (bound := fun t : ℝ => t ^ (ν.re - 1) * Real.exp (-(x₀ / 4 * (t + t⁻¹))))
    (Filter.Eventually.of_forall fun x => (hmeasF x).aestronglyMeasurable) ?_ ?_ ?_
  ·
    filter_upwards [Ioi_mem_nhds (show x₀ / 2 < x₀ by linarith)] with x hx
    have hx : x₀ / 2 < x := hx
    refine (ae_restrict_mem measurableSet_Ioi).mono (fun t ht => ?_)
    have ht : 0 < t := ht
    rw [norm_besselIntegrand ν x t ht]
    have hsum : 0 < t + t⁻¹ := by positivity
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg ht.le _)
    apply Real.exp_le_exp.mpr
    nlinarith
  · exact integrableOn_rpow_mul_exp_neg_mul_add_inv (by linarith) ν.re
  · refine (ae_restrict_mem measurableSet_Ioi).mono (fun t _ => ?_)
    exact ((Complex.continuous_ofReal.comp (Real.continuous_exp.comp
      ((continuous_id.mul continuous_const).div_const 2).neg)).mul continuous_const).continuousAt

def F (ν s : ℂ) (p : ℝ × ℝ) : ℂ :=
  (p.1 : ℂ) ^ (s - 1) * (((Real.exp (-(p.1 * (p.2 + p.2⁻¹) / 2)) : ℝ) : ℂ) * ((p.2 : ℂ) ^ (ν - 1)))

theorem measurable_F (ν s : ℂ) : Measurable (F ν s) := by
  unfold F
  refine ((Complex.measurable_ofReal.comp measurable_fst).pow_const _).mul
    ((Complex.measurable_ofReal.comp (Real.measurable_exp.comp ?_)).mul
      ((Complex.measurable_ofReal.comp measurable_snd).pow_const _))
  exact ((measurable_fst.mul (measurable_snd.add measurable_snd.inv)).div_const 2).neg

theorem F_eq (ν s : ℂ) (x t : ℝ) :
    F ν s (x, t) = (t : ℂ) ^ (ν - 1) *
      ((x : ℂ) ^ (s - 1) * Complex.exp (-((((t + t⁻¹) / 2 : ℝ) : ℂ) * (x : ℂ)))) := by
  simp only [F, Complex.ofReal_exp]
  push_cast
  ring_nf

theorem norm_F (ν s : ℂ) {x t : ℝ} (hx : 0 < x) (ht : 0 < t) :
    ‖F ν s (x, t)‖ = t ^ (ν.re - 1) * (x ^ (s.re - 1) * Real.exp (-((t + t⁻¹) / 2 * x))) := by
  rw [F_eq, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_cpow_eq_rpow_re_of_pos hx,
    Complex.norm_exp, Complex.sub_re, Complex.one_re, Complex.sub_re, Complex.one_re]
  congr 2
  simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

theorem integrable_F (ν s : ℂ) (hs : |ν.re| < s.re) :
    Integrable (F ν s) ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hσ : 0 < s.re := lt_of_le_of_lt (abs_nonneg _) hs
  have hν1 : -s.re < ν.re := by have := neg_abs_le ν.re; linarith
  have hν2 : ν.re < s.re := lt_of_le_of_lt (le_abs_self _) hs
  rw [integrable_prod_iff' (measurable_F ν s).aestronglyMeasurable]
  constructor
  · refine (ae_restrict_mem measurableSet_Ioi).mono (fun t ht => ?_)
    have ht : 0 < t := ht
    have hc : 0 < (t + t⁻¹) / 2 := by positivity
    have h1 := (integrableOn_cpow_mul_exp_neg_mul (a := s) hσ hc).const_mul ((t : ℂ) ^ (ν - 1))
    exact IntegrableOn.congr_fun h1 (fun x _ => (F_eq ν s x t).symm) measurableSet_Ioi
  · have hI := (integrableOn_rpow_mul_one_add_sq_rpow_neg (p := ν.re + s.re - 1) (σ := s.re)
      (by linarith) hσ (by linarith)).const_mul ((2 : ℝ) ^ s.re * Real.Gamma s.re)
    refine IntegrableOn.congr_fun hI (fun t ht => ?_) measurableSet_Ioi
    have ht : 0 < t := ht
    have hc : 0 < (t + t⁻¹) / 2 := by positivity
    rw [setIntegral_congr_fun measurableSet_Ioi (fun x hx => norm_F ν s hx ht), integral_const_mul,
      Real.integral_rpow_mul_exp_neg_mul_Ioi hσ hc]
    have e1 : 1 / ((t + t⁻¹) / 2) = 2 * t * (1 + t ^ 2)⁻¹ := by field_simp; ring
    rw [e1, Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by norm_num) ht.le,
      Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity)]
    rw [show ν.re + s.re - 1 = (ν.re - 1) + s.re by ring, Real.rpow_add ht]
    ring

theorem mellin_besselKernel_eq_integral (ν s : ℂ) (hs : |ν.re| < s.re) :
    MellinConvergent (fun x : ℝ => besselKernel ν x) s ∧
      mellin (fun x : ℝ => besselKernel ν x) s = ∫ t in Ioi (0 : ℝ), ∫ x in Ioi (0 : ℝ), F ν s (x, t) := by
  have hF := integrable_F ν s hs
  have hpt : ∀ x : ℝ, (x : ℂ) ^ (s - 1) • besselKernel ν x = ∫ t in Ioi (0 : ℝ), F ν s (x, t) := by
    intro x
    unfold besselKernel
    rw [← integral_smul]
    rfl
  constructor
  · have h1 : Integrable (fun x : ℝ => ∫ t in Ioi (0 : ℝ), F ν s (x, t)) (volume.restrict (Ioi 0)) :=
      hF.integral_prod_left
    exact h1.congr (Filter.Eventually.of_forall fun x => (hpt x).symm)
  · unfold mellin
    rw [show (fun x : ℝ => (x : ℂ) ^ (s - 1) • besselKernel ν x) = fun x => ∫ t in Ioi (0 : ℝ), F ν s (x, t) from
      funext hpt]
    exact integral_integral_swap (f := fun x t => F ν s (x, t)) hF

def G (ν s : ℂ) (p : ℝ × ℝ) : ℂ :=
  (p.1 : ℂ) ^ (ν + s - 1) * ((p.2 : ℂ) ^ (s - 1) * Complex.exp (-((((1 + p.1 ^ 2 : ℝ)) : ℂ) * (p.2 : ℂ))))

theorem measurable_G (ν s : ℂ) : Measurable (G ν s) := by
  unfold G
  refine ((Complex.measurable_ofReal.comp measurable_fst).pow_const _).mul
    (((Complex.measurable_ofReal.comp measurable_snd).pow_const _).mul (Measurable.cexp ?_))
  exact ((Complex.measurable_ofReal.comp (measurable_const.add (measurable_fst.pow_const 2))).mul
    (Complex.measurable_ofReal.comp measurable_snd)).neg

theorem G_eq (ν s : ℂ) (t y : ℝ) :
    G ν s (t, y) = ((y : ℂ) ^ (s - 1) * Complex.exp (-(y : ℂ))) *
      ((t : ℂ) ^ (2 * ((ν + s) / 2) - 1) * Complex.exp (-((y : ℂ) * (t : ℂ) ^ 2))) := by
  simp only [G]
  have e : Complex.exp (-((((1 + t ^ 2 : ℝ)) : ℂ) * (y : ℂ))) =
      Complex.exp (-(y : ℂ)) * Complex.exp (-((y : ℂ) * (t : ℂ) ^ 2)) := by
    rw [← Complex.exp_add]; push_cast; ring_nf
  rw [e, show 2 * ((ν + s) / 2) - 1 = ν + s - 1 by ring]
  ring

theorem norm_G (ν s : ℂ) {t y : ℝ} (ht : 0 < t) (hy : 0 < y) :
    ‖G ν s (t, y)‖ = (y ^ (s.re - 1) * Real.exp (-y)) *
      (t ^ (2 * ((ν.re + s.re) / 2) - 1) * Real.exp (-(y * t ^ 2))) := by
  rw [G_eq, norm_mul, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht,
    Complex.norm_cpow_eq_rpow_re_of_pos hy, Complex.norm_exp, Complex.norm_exp]
  simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re,
    Complex.one_re, Complex.add_re, Complex.div_ofNat_re, zero_mul, sub_zero,
    show ((t : ℂ) ^ 2).re = t ^ 2 by rw [← Complex.ofReal_pow]; exact Complex.ofReal_re _,
    show ((t : ℂ) ^ 2).im = 0 by rw [← Complex.ofReal_pow]; exact Complex.ofReal_im _]
  congr 2
  · congr 1
    simp only [Complex.re_ofNat, Complex.im_ofNat, Complex.add_re, Complex.div_ofNat_im, zero_mul, sub_zero]

theorem integrable_G (ν s : ℂ) (hs : |ν.re| < s.re) :
    Integrable (G ν s) ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hσ : 0 < s.re := lt_of_le_of_lt (abs_nonneg _) hs
  have ha : 0 < (ν.re + s.re) / 2 := by have := neg_abs_le ν.re; linarith
  have hb : 0 < (s.re - ν.re) / 2 := by have := le_abs_self ν.re; linarith
  rw [integrable_prod_iff' (measurable_G ν s).aestronglyMeasurable]
  constructor
  · refine (ae_restrict_mem measurableSet_Ioi).mono (fun y hy => ?_)
    have hy : 0 < y := hy
    have h1 := (integrableOn_rpow_mul_exp_neg_mul_sq ha hy).const_mul (y ^ (s.re - 1) * Real.exp (-y))
    refine h1.mono' ((measurable_G ν s).comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable ?_
    refine (ae_restrict_mem measurableSet_Ioi).mono (fun t ht => ?_)
    rw [norm_G ν s ht hy]
  · have hI := (integrableOn_rpow_mul_exp_neg_mul hb one_pos).const_mul
      (1 / 2 * Real.Gamma ((ν.re + s.re) / 2))
    refine IntegrableOn.congr_fun hI (fun y hy => ?_) measurableSet_Ioi
    have hy : 0 < y := hy
    rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => norm_G ν s ht hy), integral_const_mul,
      integral_rpow_mul_exp_neg_mul_sq ha hy, one_div y, Real.inv_rpow hy.le, ← Real.rpow_neg hy.le,
      one_mul]
    have e : y ^ (s.re - 1) * y ^ (-((ν.re + s.re) / 2)) = y ^ ((s.re - ν.re) / 2 - 1) := by
      rw [← Real.rpow_add hy]; congr 1; ring
    rw [← e]
    ring

theorem integral_G_snd (ν s : ℂ) (hσ : 0 < s.re) {t : ℝ} (ht : 0 < t) :
    ∫ y in Ioi (0 : ℝ), G ν s (t, y) =
      (t : ℂ) ^ (ν + s - 1) * ((1 / (((1 + t ^ 2 : ℝ)) : ℂ)) ^ s * Complex.Gamma s) := by
  rw [show (fun y : ℝ => G ν s (t, y)) = fun y : ℝ => (t : ℂ) ^ (ν + s - 1) *
      ((y : ℂ) ^ (s - 1) * Complex.exp (-((((1 + t ^ 2 : ℝ)) : ℂ) * (y : ℂ)))) from rfl,
    integral_const_mul, Complex.integral_cpow_mul_exp_neg_mul_Ioi hσ (by positivity)]

theorem integral_G_fst (ν s : ℂ) (hs : |ν.re| < s.re) {y : ℝ} (hy : 0 < y) :
    ∫ t in Ioi (0 : ℝ), G ν s (t, y) =
      ((y : ℂ) ^ (s - 1) * Complex.exp (-(y : ℂ))) *
        ((1 / 2 : ℂ) * ((1 / (y : ℂ)) ^ ((ν + s) / 2) * Complex.Gamma ((ν + s) / 2))) := by
  have ha : 0 < ((ν + s) / 2).re := by
    simp only [Complex.add_re, Complex.div_ofNat_re]
    have := neg_abs_le ν.re; linarith
  rw [show (fun t : ℝ => G ν s (t, y)) = fun t : ℝ => ((y : ℂ) ^ (s - 1) * Complex.exp (-(y : ℂ))) *
      ((t : ℂ) ^ (2 * ((ν + s) / 2) - 1) * Complex.exp (-((y : ℂ) * (t : ℂ) ^ 2))) from funext fun t => G_eq ν s t y,
    integral_const_mul, integral_cpow_mul_exp_neg_mul_sq ha hy]

theorem integral_G_swap (ν s : ℂ) (hs : |ν.re| < s.re) :
    ∫ t in Ioi (0 : ℝ), ∫ y in Ioi (0 : ℝ), G ν s (t, y) = ∫ y in Ioi (0 : ℝ), ∫ t in Ioi (0 : ℝ), G ν s (t, y) :=
  integral_integral_swap (f := fun t y => G ν s (t, y)) (integrable_G ν s hs)

end LanglandsTunnell.ArchBessel.MellinK

end

open LanglandsTunnell.ArchBessel.MellinK in
theorem solution (ν s : ℂ) (hs : |ν.re| < s.re) :
    MellinConvergent (fun x : ℝ => besselKernel ν x) s ∧
      mellin (fun x : ℝ => besselKernel ν x) s =
        (2 : ℂ) ^ (s - 1) * Complex.Gamma ((s + ν) / 2) * Complex.Gamma ((s - ν) / 2) := by
  have hσ : 0 < s.re := lt_of_le_of_lt (abs_nonneg _) hs
  have ha : 0 < ((ν + s) / 2).re := by
    simp only [Complex.add_re, Complex.div_ofNat_re]; have := neg_abs_le ν.re; linarith
  have hb : 0 < ((s - ν) / 2).re := by
    simp only [Complex.sub_re, Complex.div_ofNat_re]; have := le_abs_self ν.re; linarith
  have h20 : (2 : ℂ) ≠ 0 := two_ne_zero
  obtain ⟨hconv, hmel⟩ := mellin_besselKernel_eq_integral ν s hs
  refine ⟨hconv, ?_⟩
  rw [hmel]

  have step1 : ∫ t in Ioi (0 : ℝ), ∫ x in Ioi (0 : ℝ), F ν s (x, t) =
      ∫ t in Ioi (0 : ℝ), (2 : ℂ) ^ s * ∫ y in Ioi (0 : ℝ), G ν s (t, y) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    have ht : 0 < t := ht
    have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
    have hc : 0 < (t + t⁻¹) / 2 := by positivity
    rw [show (fun x : ℝ => F ν s (x, t)) = fun x : ℝ => (t : ℂ) ^ (ν - 1) *
        ((x : ℂ) ^ (s - 1) * Complex.exp (-((((t + t⁻¹) / 2 : ℝ) : ℂ) * (x : ℂ)))) from funext fun x => F_eq ν s x t,
      integral_const_mul, Complex.integral_cpow_mul_exp_neg_mul_Ioi hσ hc, integral_G_snd ν s hσ ht]

    have e1 : (1 : ℂ) / ((((t + t⁻¹) / 2 : ℝ)) : ℂ) = (((2 * t : ℝ)) : ℂ) * ((((1 + t ^ 2)⁻¹ : ℝ)) : ℂ) := by
      have : (1 : ℝ) / ((t + t⁻¹) / 2) = (2 * t) * (1 + t ^ 2)⁻¹ := by field_simp; ring
      rw [← Complex.ofReal_mul, ← this]; push_cast; ring
    have e2 : ((((2 * t : ℝ)) : ℂ) * ((((1 + t ^ 2)⁻¹ : ℝ)) : ℂ)) ^ s =
        (2 : ℂ) ^ s * (t : ℂ) ^ s * ((1 : ℂ) / (((1 + t ^ 2 : ℝ)) : ℂ)) ^ s := by
      rw [Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity),
        show (((2 * t : ℝ)) : ℂ) = (((2 : ℝ)) : ℂ) * ((t : ℝ) : ℂ) by push_cast; ring,
        Complex.mul_cpow_ofReal_nonneg (by norm_num) ht.le]
      push_cast
      ring_nf
    rw [e1, e2]
    have e3 : (t : ℂ) ^ (ν - 1) * (t : ℂ) ^ s = (t : ℂ) ^ (ν + s - 1) := by
      rw [← Complex.cpow_add _ _ ht0]; congr 1; ring
    calc (t : ℂ) ^ (ν - 1) * ((2 : ℂ) ^ s * (t : ℂ) ^ s * ((1 : ℂ) / (((1 + t ^ 2 : ℝ)) : ℂ)) ^ s * Complex.Gamma s)
        = (2 : ℂ) ^ s * (((t : ℂ) ^ (ν - 1) * (t : ℂ) ^ s) * (((1 : ℂ) / (((1 + t ^ 2 : ℝ)) : ℂ)) ^ s * Complex.Gamma s)) := by
          ring
      _ = _ := by rw [e3]
  rw [step1, integral_const_mul, integral_G_swap ν s hs]

  have step2 : ∫ y in Ioi (0 : ℝ), ∫ t in Ioi (0 : ℝ), G ν s (t, y) =
      ∫ y in Ioi (0 : ℝ), ((1 / 2 : ℂ) * Complex.Gamma ((ν + s) / 2)) *
        ((y : ℂ) ^ ((s - ν) / 2 - 1) * Complex.exp (-((((1 : ℝ)) : ℂ) * (y : ℂ)))) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun y hy => ?_)
    have hy : 0 < y := hy
    have hy0 : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
    rw [integral_G_fst ν s hs hy]
    have e1 : ((1 : ℂ) / (y : ℂ)) ^ ((ν + s) / 2) = (y : ℂ) ^ (-((ν + s) / 2)) := by
      rw [one_div, Complex.inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg hy.le]; exact Real.pi_ne_zero.symm),
        Complex.cpow_neg]
    have e2 : (y : ℂ) ^ (s - 1) * (y : ℂ) ^ (-((ν + s) / 2)) = (y : ℂ) ^ ((s - ν) / 2 - 1) := by
      rw [← Complex.cpow_add _ _ hy0]; congr 1; ring
    rw [e1]
    push_cast
    rw [one_mul]
    calc (y : ℂ) ^ (s - 1) * Complex.exp (-(y : ℂ)) * (1 / 2 * ((y : ℂ) ^ (-((ν + s) / 2)) * Complex.Gamma ((ν + s) / 2)))
        = 1 / 2 * Complex.Gamma ((ν + s) / 2) * (((y : ℂ) ^ (s - 1) * (y : ℂ) ^ (-((ν + s) / 2))) *
            Complex.exp (-(y : ℂ))) := by ring
      _ = _ := by rw [e2]
  rw [step2, integral_const_mul, Complex.integral_cpow_mul_exp_neg_mul_Ioi hb one_pos]
  push_cast
  rw [div_one, Complex.one_cpow, one_mul, show (ν + s) / 2 = (s + ν) / 2 by ring]
  have e : (2 : ℂ) ^ s * (1 / 2) = (2 : ℂ) ^ (s - 1) := by
    rw [Complex.cpow_sub _ _ h20, Complex.cpow_one]; ring
  calc (2 : ℂ) ^ s * (1 / 2 * Complex.Gamma ((s + ν) / 2) * Complex.Gamma ((s - ν) / 2))
      = ((2 : ℂ) ^ s * (1 / 2)) * Complex.Gamma ((s + ν) / 2) * Complex.Gamma ((s - ν) / 2) := by ring
    _ = _ := by rw [e]

#print axioms solution

end S_LanglandsTunnell_ArchBessel_mellin_besselKernel_eq_mul_Gamma_mul_Gamma
end P2MW
export P2MW.S_LanglandsTunnell_ArchBessel_mellin_besselKernel_eq_mul_Gamma_mul_Gamma (solution)
