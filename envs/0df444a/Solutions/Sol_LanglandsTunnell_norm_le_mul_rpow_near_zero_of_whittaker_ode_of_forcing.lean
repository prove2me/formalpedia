-- Prove2me | solution 1 for LanglandsTunnell.norm_le_mul_rpow_near_zero_of_whittaker_ode_of_forcing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/5da35445-d981-587a-96b1-341559332296

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_norm_le_mul_rpow_near_zero_of_whittaker_ode_of_forcing

set_option autoImplicit false

open scoped Real

namespace GluePNearZero41F

private noncomputable def eA (t : ℝ) : ℝ := Real.exp (-t)
private noncomputable def eB (t : ℝ) : ℝ := Real.exp (t / 2)

private lemma eA_pos (t : ℝ) : 0 < eA t := Real.exp_pos _
private lemma eB_pos (t : ℝ) : 0 < eB t := Real.exp_pos _
private lemma eA_le_one {t : ℝ} (ht : 0 ≤ t) : eA t ≤ 1 := by
  unfold eA; exact Real.exp_le_one_iff.mpr (by linarith)
private lemma eA_zero : eA 0 = 1 := by simp [eA]
private lemma eB_sq (t : ℝ) : eB t ^ 2 = Real.exp t := by
  unfold eB; rw [← Real.exp_nat_mul]; congr 1; ring
private lemma eA_mul_eB_sq (t : ℝ) : eA t * eB t ^ 2 = 1 := by
  rw [eB_sq]; unfold eA; rw [← Real.exp_add]; simp

private lemma eA_hasDerivAt (t : ℝ) : HasDerivAt eA (-(eA t)) t := by
  have h : HasDerivAt (fun x : ℝ => Real.exp (-x)) (Real.exp (-t) * (-1)) t := (hasDerivAt_neg t).exp
  unfold eA; simpa using h
private lemma eB_hasDerivAt (t : ℝ) : HasDerivAt eB (eB t / 2) t := by
  have h : HasDerivAt (fun x : ℝ => Real.exp (x / 2)) (Real.exp (t / 2) * (1 / 2)) t := by
    have h0 : HasDerivAt (fun x : ℝ => x / 2) (1 / 2) t := by
      simpa using (hasDerivAt_id t).div_const (2 : ℝ)
    exact h0.exp
  unfold eB; convert h using 1; ring

private noncomputable def Gf (f : ℝ → ℂ) (t : ℝ) : ℂ := (eB t : ℂ) * f (eA t)

private noncomputable def Hf (f : ℝ → ℂ) (t : ℝ) : ℂ := (eA t : ℂ) * (eB t : ℂ) * deriv f (eA t)
private noncomputable def vp (l : ℂ) (f : ℝ → ℂ) (t : ℝ) : ℂ := (1 / 2 + l) * Gf f t - Hf f t
private noncomputable def vm (l : ℂ) (f : ℝ → ℂ) (t : ℝ) : ℂ := (1 / 2 - l) * Gf f t - Hf f t

private noncomputable def Ff (h : ℝ → ℂ) (t : ℝ) : ℂ := (eB t : ℂ) * h (eA t)
private noncomputable def sfun (ν l : ℂ) (k : ℝ) (t : ℝ) : ℂ :=
  ν ^ 2 - l ^ 2 + 4 * (π : ℂ) ^ 2 * ((eA t : ℝ) : ℂ) ^ 2 - 2 * (π : ℂ) * (k : ℂ) * ((eA t : ℝ) : ℂ)

private lemma vp_sub_vm (l : ℂ) (f : ℝ → ℂ) (t : ℝ) : vp l f t - vm l f t = 2 * l * Gf f t := by
  unfold vp vm; ring

section derivs

variable (f : ℝ → ℂ) (hf : DifferentiableOn ℝ f (Set.Ioi 0)) (hf' : DifferentiableOn ℝ (deriv f) (Set.Ioi 0))
include hf hf'

omit hf' in
private lemma Gf_hasDerivAt (t : ℝ) :
    HasDerivAt (Gf f) (((eB t / 2 : ℝ) : ℂ) * f (eA t) + (eB t : ℂ) * (((-(eA t) : ℝ) : ℂ) * deriv f (eA t))) t := by
  have hy : eA t ∈ Set.Ioi (0 : ℝ) := eA_pos t
  have h1 : HasDerivAt (fun x : ℝ => ((eB x : ℝ) : ℂ)) ((eB t / 2 : ℝ) : ℂ) t := (eB_hasDerivAt t).ofReal_comp
  have hfy : HasDerivAt f (deriv f (eA t)) (eA t) :=
    ((hf.differentiableAt (Ioi_mem_nhds (eA_pos t))).hasDerivAt)
  have h2 : HasDerivAt (fun x : ℝ => f (eA x)) ((-(eA t)) • deriv f (eA t)) t := hfy.scomp t (eA_hasDerivAt t)
  have h3 := h1.mul h2
  unfold Gf
  convert h3 using 1
  rfl
  rfl
  rfl

omit hf in
private lemma Hf_hasDerivAt (t : ℝ) :
    HasDerivAt (Hf f)
      ((((-(eA t) : ℝ) : ℂ) * (eB t : ℂ) + (eA t : ℂ) * ((eB t / 2 : ℝ) : ℂ)) * deriv f (eA t)
        + (eA t : ℂ) * (eB t : ℂ) * (((-(eA t) : ℝ) : ℂ) * deriv (deriv f) (eA t))) t := by
  have h1 : HasDerivAt (fun x : ℝ => ((eA x : ℝ) : ℂ)) ((-(eA t) : ℝ) : ℂ) t := (eA_hasDerivAt t).ofReal_comp
  have h2 : HasDerivAt (fun x : ℝ => ((eB x : ℝ) : ℂ)) ((eB t / 2 : ℝ) : ℂ) t := (eB_hasDerivAt t).ofReal_comp
  have hfy : HasDerivAt (deriv f) (deriv (deriv f) (eA t)) (eA t) :=
    ((hf'.differentiableAt (Ioi_mem_nhds (eA_pos t))).hasDerivAt)
  have h3 : HasDerivAt (fun x : ℝ => deriv f (eA x)) ((-(eA t)) • deriv (deriv f) (eA t)) t :=
    hfy.scomp t (eA_hasDerivAt t)
  have h4 := (h1.mul h2).mul h3
  unfold Hf
  convert h4 using 1
  rfl
  rfl
  rfl

variable (ν : ℂ) (k : ℝ) (h : ℝ → ℂ)
variable (hfeq : ∀ y : ℝ, 0 < y →
    (y : ℂ) ^ 2 * deriv (deriv f) y
      + (1 / 4 - ν ^ 2 + 2 * (π : ℂ) * (k : ℂ) * (y : ℂ) - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2) * f y = h y)
include hfeq

private lemma vp_hasDerivAt (l : ℂ) (t : ℝ) :
    HasDerivAt (vp l f) (l * vp l f t + (sfun ν l k t * Gf f t + Ff h t)) t := by
  have hG := Gf_hasDerivAt f hf t
  have hH := Hf_hasDerivAt f hf' t
  have h := (hG.const_mul (1 / 2 + l)).sub hH
  have hode := hfeq (eA t) (eA_pos t)
  refine (h.congr_deriv ?_)
  unfold vp Gf Hf sfun Ff
  push_cast
  linear_combination ((eB t : ℝ) : ℂ) * hode

private lemma vm_hasDerivAt (l : ℂ) (t : ℝ) :
    HasDerivAt (vm l f) (-l * vm l f t + (sfun ν l k t * Gf f t + Ff h t)) t := by
  have hG := Gf_hasDerivAt f hf t
  have hH := Hf_hasDerivAt f hf' t
  have h := (hG.const_mul (1 / 2 - l)).sub hH
  have hode := hfeq (eA t) (eA_pos t)
  refine (h.congr_deriv ?_)
  unfold vm Gf Hf sfun Ff
  push_cast
  linear_combination ((eB t : ℝ) : ℂ) * hode

end derivs

private noncomputable def nsq (v : ℝ → ℂ) (t : ℝ) : ℝ := (v t).re * (v t).re + (v t).im * (v t).im

private lemma nsq_eq (v : ℝ → ℂ) (t : ℝ) : nsq v t = ‖v t‖ ^ 2 := by
  unfold nsq; rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]

private lemma nsq_hasDerivAt {v : ℝ → ℂ} {v' : ℂ} {t : ℝ} (hv : HasDerivAt v v' t) :
    HasDerivAt (nsq v) (2 * ((v t).re * v'.re + (v t).im * v'.im)) t := by
  have hre : HasDerivAt (fun x => (v x).re) v'.re t := by
    have := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hv
    simp at this
    exact this
  have him : HasDerivAt (fun x => (v x).im) v'.im t := by
    have := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hv
    simp at this
    exact this
  have h := (hre.mul hre).add (him.mul him)
  unfold nsq
  convert h using 1
  · rfl
  · rfl
  · rfl
  ring

private lemma cross_le (v w : ℂ) : v.re * w.re + v.im * w.im ≤ ‖v‖ * ‖w‖ := by
  have h1 : v.re * w.re + v.im * w.im = ((starRingEnd ℂ) v * w).re := by
    simp [Complex.mul_re]
  have h2 : ((starRingEnd ℂ) v * w).re ≤ ‖(starRingEnd ℂ) v * w‖ := Complex.re_le_norm _
  rw [h1]; refine h2.trans (le_of_eq ?_); rw [norm_mul, Complex.norm_conj]

private lemma cross_decomp (v c w : ℂ) :
    v.re * (c * v + w).re + v.im * (c * v + w).im
      = c.re * (v.re * v.re + v.im * v.im) + (v.re * w.re + v.im * w.im) := by
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]; ring

private lemma rate_bound (p q g S m lre Li cp cm : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hg0 : 0 ≤ g) (hS : 0 ≤ S)
    (hSm : S ≤ m) (hLi : 0 ≤ Li) (hg : 2 * g ≤ Li * (p + q)) (hcp : cp ≤ p * (S * g)) (hcm : cm ≤ q * (S * g)) :
    2 * (lre * (p * p) + cp) + 2 * ((-lre) * (q * q) + cm) ≤ (2 * |lre| + 2 * Li * m) * (p * p + q * q) := by
  have hl1 : lre ≤ |lre| := le_abs_self lre
  have hl2 : -lre ≤ |lre| := neg_le_abs lre
  have hpq : 0 ≤ p * p := mul_nonneg hp hp
  have hqq : 0 ≤ q * q := mul_nonneg hq hq

  have hSg : 0 ≤ S * g := mul_nonneg hS hg0
  have h1 : cp + cm ≤ S * g * (p + q) := by nlinarith
  have h2 : 2 * (S * g * (p + q)) ≤ S * (Li * (p + q)) * (p + q) := by
    have := mul_le_mul_of_nonneg_left hg (mul_nonneg hS (add_nonneg hp hq))
    nlinarith
  have h3 : S * (Li * (p + q)) * (p + q) ≤ S * Li * (2 * (p * p + q * q)) := by
    have hsq : (p + q) * (p + q) ≤ 2 * (p * p + q * q) := by nlinarith [mul_self_nonneg (p - q)]
    have hSL : 0 ≤ S * Li := mul_nonneg hS hLi
    nlinarith [mul_le_mul_of_nonneg_left hsq hSL]
  have h4 : S * Li * (2 * (p * p + q * q)) ≤ m * Li * (2 * (p * p + q * q)) := by
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hSm hLi)
      (by positivity : (0:ℝ) ≤ 2 * (p * p + q * q))
    linarith
  have hdiag : 2 * (lre * (p * p)) + 2 * ((-lre) * (q * q)) ≤ 2 * |lre| * (p * p + q * q) := by
    nlinarith [mul_le_mul_of_nonneg_right hl1 hpq, mul_le_mul_of_nonneg_right hl2 hqq]
  nlinarith [h1, h2, h3, h4, hdiag]

private lemma rate_bound_forced (p q g S m lre Li cp cm φ η : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hg0 : 0 ≤ g)
    (hS : 0 ≤ S) (hSm : S ≤ m) (hLi : 0 ≤ Li) (hg : 2 * g ≤ Li * (p + q)) (hη : 0 < η)
    (hcp : cp ≤ p * (S * g + φ)) (hcm : cm ≤ q * (S * g + φ)) :
    2 * (lre * (p * p) + cp) + 2 * ((-lre) * (q * q) + cm)
      ≤ (2 * |lre| + 2 * Li * m + η) * (p * p + q * q) + 2 * η⁻¹ * (φ * φ) := by
  have h0 := rate_bound p q g S m lre Li (cp - p * φ) (cm - q * φ) hp hq hg0 hS hSm hLi hg
    (by linarith [hcp, mul_add p (S * g) φ]) (by linarith [hcm, mul_add q (S * g) φ])
  have hθ : η⁻¹ * η = 1 := inv_mul_cancel₀ hη.ne'
  have hθ0 : 0 ≤ η⁻¹ := inv_nonneg.mpr hη.le
  have amgm : ∀ r : ℝ, 2 * r * φ ≤ η * (r * r) + η⁻¹ * (φ * φ) := by
    intro r
    have h1 : η * (2 * r * φ) ≤ η * η * (r * r) + φ * φ := by nlinarith [sq_nonneg (η * r - φ)]
    have h2 : η⁻¹ * (η * (2 * r * φ)) ≤ η⁻¹ * (η * η * (r * r) + φ * φ) := mul_le_mul_of_nonneg_left h1 hθ0
    calc 2 * r * φ = η⁻¹ * η * (2 * r * φ) := by rw [hθ, one_mul]
      _ = η⁻¹ * (η * (2 * r * φ)) := by ring
      _ ≤ η⁻¹ * (η * η * (r * r) + φ * φ) := h2
      _ = η⁻¹ * η * η * (r * r) + η⁻¹ * (φ * φ) := by ring
      _ = η * (r * r) + η⁻¹ * (φ * φ) := by rw [hθ, one_mul]
  have hp' := amgm p
  have hq' := amgm q
  linarith [h0, hp', hq']

private lemma sq_assemble {a b c e M y r : ℝ} (hy : 0 ≤ y) (hc : 0 ≤ c) (h1 : a = y * b) (h2 : b ≤ c * e)
    (h3 : e ≤ M * r) : a ≤ c * M * (y * r) := by
  rw [h1]
  have h4 : b ≤ c * (M * r) := h2.trans (mul_le_mul_of_nonneg_left h3 hc)
  have h5 := mul_le_mul_of_nonneg_left h4 hy
  calc y * b ≤ y * (c * (M * r)) := h5
    _ = c * M * (y * r) := by ring

section energy

variable (ν l : ℂ) (k : ℝ) (f h : ℝ → ℂ)
variable (hf : DifferentiableOn ℝ f (Set.Ioi 0)) (hf' : DifferentiableOn ℝ (deriv f) (Set.Ioi 0))
variable (hfeq : ∀ y : ℝ, 0 < y →
    (y : ℂ) ^ 2 * deriv (deriv f) y
      + (1 / 4 - ν ^ 2 + 2 * (π : ℂ) * (k : ℂ) * (y : ℂ) - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2) * f y = h y)

private noncomputable def Efun (t : ℝ) : ℝ := nsq (vp l f) t + nsq (vm l f) t

private lemma Efun_nonneg (t : ℝ) : 0 ≤ Efun l f t := by
  unfold Efun; rw [nsq_eq, nsq_eq]; positivity

private noncomputable def mfun (m₀ : ℝ) (t : ℝ) : ℝ := m₀ + 2 * π * |k| * eA t + 4 * π ^ 2 * (eA t * eA t)

private lemma norm_sfun_le (m₀ : ℝ) (hm₀ : ‖ν ^ 2 - l ^ 2‖ ≤ m₀) (t : ℝ) : ‖sfun ν l k t‖ ≤ mfun k m₀ t := by
  unfold sfun mfun
  have hA : 0 ≤ eA t := (eA_pos t).le
  have hpi : ‖(π : ℂ)‖ = π := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have hk : ‖(k : ℂ)‖ = |k| := by rw [Complex.norm_real, Real.norm_eq_abs]
  have hAn : ‖((eA t : ℝ) : ℂ)‖ = eA t := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hA]
  have h4 : ‖(4 : ℂ)‖ = 4 := by simp
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  calc ‖ν ^ 2 - l ^ 2 + 4 * (π : ℂ) ^ 2 * ((eA t : ℝ) : ℂ) ^ 2 - 2 * (π : ℂ) * (k : ℂ) * ((eA t : ℝ) : ℂ)‖
      ≤ ‖ν ^ 2 - l ^ 2 + 4 * (π : ℂ) ^ 2 * ((eA t : ℝ) : ℂ) ^ 2‖ + ‖2 * (π : ℂ) * (k : ℂ) * ((eA t : ℝ) : ℂ)‖ :=
        norm_sub_le _ _
    _ ≤ (‖ν ^ 2 - l ^ 2‖ + ‖4 * (π : ℂ) ^ 2 * ((eA t : ℝ) : ℂ) ^ 2‖) + ‖2 * (π : ℂ) * (k : ℂ) * ((eA t : ℝ) : ℂ)‖ := by
        gcongr; exact norm_add_le _ _
    _ = (‖ν ^ 2 - l ^ 2‖ + 4 * π ^ 2 * (eA t * eA t)) + 2 * π * |k| * eA t := by
        rw [norm_mul, norm_mul, norm_pow, norm_pow, h4, hpi, hAn, norm_mul, norm_mul, norm_mul, h2, hpi, hk, hAn]; ring
    _ ≤ (m₀ + 4 * π ^ 2 * (eA t * eA t)) + 2 * π * |k| * eA t := by gcongr
    _ = m₀ + 2 * π * |k| * eA t + 4 * π ^ 2 * (eA t * eA t) := by ring

private noncomputable def rate (m₀ : ℝ) (t : ℝ) : ℝ := 2 * |l.re| + 2 * ‖l‖⁻¹ * mfun k m₀ t

include hf hf' hfeq in
private lemma Efun_hasDerivAt_le (hl : l ≠ 0) (m₀ : ℝ) (hm₀ : ‖ν ^ 2 - l ^ 2‖ ≤ m₀) (η : ℝ) (hη : 0 < η) (t : ℝ) :
    ∃ E' : ℝ, HasDerivAt (Efun l f) E' t ∧
      E' ≤ (rate l k m₀ t + η) * Efun l f t + 2 * η⁻¹ * ‖Ff h t‖ ^ 2 := by
  have hvp := vp_hasDerivAt f hf hf' ν k h hfeq l t
  have hvm := vm_hasDerivAt f hf hf' ν k h hfeq l t
  have hEp := nsq_hasDerivAt hvp
  have hEm := nsq_hasDerivAt hvm
  refine ⟨_, hEp.add hEm, ?_⟩

  set w := sfun ν l k t * Gf f t + Ff h t with hw
  have hdp := cross_decomp (vp l f t) l w
  have hdm := cross_decomp (vm l f t) (-l) w
  have hcp := cross_le (vp l f t) w
  have hcm := cross_le (vm l f t) w
  have hwn : ‖w‖ ≤ ‖sfun ν l k t‖ * ‖Gf f t‖ + ‖Ff h t‖ := by
    rw [hw]; exact (norm_add_le _ _).trans (by rw [norm_mul])
  have hS := norm_sfun_le ν l k m₀ hm₀ t
  have hS0 : 0 ≤ ‖sfun ν l k t‖ := norm_nonneg _
  have hLi : 0 ≤ ‖l‖⁻¹ := inv_nonneg.mpr (norm_nonneg _)
  have hl0 : 0 < ‖l‖ := norm_pos_iff.mpr hl

  have hg : 2 * ‖Gf f t‖ ≤ ‖l‖⁻¹ * (‖vp l f t‖ + ‖vm l f t‖) := by
    have h1 : ‖vp l f t - vm l f t‖ ≤ ‖vp l f t‖ + ‖vm l f t‖ := norm_sub_le _ _
    rw [vp_sub_vm, norm_mul, norm_mul] at h1
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    rw [h2] at h1
    have h3 := mul_le_mul_of_nonneg_left h1 hLi
    calc 2 * ‖Gf f t‖ = ‖l‖⁻¹ * (2 * ‖l‖ * ‖Gf f t‖) := by field_simp
      _ ≤ ‖l‖⁻¹ * (‖vp l f t‖ + ‖vm l f t‖) := h3
  have hcp' : (vp l f t).re * w.re + (vp l f t).im * w.im ≤ ‖vp l f t‖ * (‖sfun ν l k t‖ * ‖Gf f t‖ + ‖Ff h t‖) :=
    hcp.trans (mul_le_mul_of_nonneg_left hwn (norm_nonneg _))
  have hcm' : (vm l f t).re * w.re + (vm l f t).im * w.im ≤ ‖vm l f t‖ * (‖sfun ν l k t‖ * ‖Gf f t‖ + ‖Ff h t‖) :=
    hcm.trans (mul_le_mul_of_nonneg_left hwn (norm_nonneg _))
  have hmain := rate_bound_forced ‖vp l f t‖ ‖vm l f t‖ ‖Gf f t‖ ‖sfun ν l k t‖ (mfun k m₀ t) l.re ‖l‖⁻¹
    ((vp l f t).re * w.re + (vp l f t).im * w.im) ((vm l f t).re * w.re + (vm l f t).im * w.im) ‖Ff h t‖ η
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hS0 hS hLi hg hη hcp' hcm'

  have hnp : (vp l f t).re * (vp l f t).re + (vp l f t).im * (vp l f t).im = ‖vp l f t‖ * ‖vp l f t‖ := by
    have := nsq_eq (vp l f) t; unfold nsq at this; rw [this]; ring
  have hnm : (vm l f t).re * (vm l f t).re + (vm l f t).im * (vm l f t).im = ‖vm l f t‖ * ‖vm l f t‖ := by
    have := nsq_eq (vm l f) t; unfold nsq at this; rw [this]; ring
  have hEt : Efun l f t = ‖vp l f t‖ * ‖vp l f t‖ + ‖vm l f t‖ * ‖vm l f t‖ := by
    unfold Efun; rw [nsq_eq, nsq_eq]; ring
  have hF2 : ‖Ff h t‖ ^ 2 = ‖Ff h t‖ * ‖Ff h t‖ := sq _
  rw [hEt, hF2]
  unfold rate
  simp only [Complex.neg_re] at hdm
  rw [hdp, hdm, hnp, hnm]
  linarith [hmain]

private noncomputable def Phi (m₀ : ℝ) (t : ℝ) : ℝ :=
  2 * |l.re| * t + 2 * ‖l‖⁻¹ * (m₀ * t + 2 * π * |k| * (1 - eA t) + 4 * π ^ 2 / 2 * (1 - eA t * eA t))

private lemma Phi_hasDerivAt (m₀ : ℝ) (t : ℝ) : HasDerivAt (Phi l k m₀) (rate l k m₀ t) t := by
  have hA := eA_hasDerivAt t
  have h1 : HasDerivAt (fun x : ℝ => 1 - eA x) (-(-(eA t))) t := hA.const_sub 1
  have h2 : HasDerivAt (fun x : ℝ => 1 - eA x * eA x) (-((-(eA t)) * eA t + eA t * (-(eA t)))) t :=
    (hA.mul hA).const_sub 1
  have h3 : HasDerivAt (fun x : ℝ => m₀ * x) (m₀ * 1) t := (hasDerivAt_id t).const_mul m₀
  have h4 : HasDerivAt (fun x : ℝ => 2 * |l.re| * x) (2 * |l.re| * 1) t := (hasDerivAt_id t).const_mul _
  have h := h4.add ((((h3.add (h1.const_mul (2 * π * |k|))).add (h2.const_mul (4 * π ^ 2 / 2)))).const_mul (2 * ‖l‖⁻¹))
  unfold Phi rate mfun
  convert h using 1
  · rfl
  · rfl
  · rfl
  ring

private lemma Phi_zero (m₀ : ℝ) : Phi l k m₀ 0 = 0 := by
  unfold Phi; rw [eA_zero]; ring

private lemma Phi_le (m₀ : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    Phi l k m₀ t ≤ (2 * |l.re| + 2 * ‖l‖⁻¹ * m₀) * t + 2 * ‖l‖⁻¹ * (2 * π * |k| + 4 * π ^ 2 / 2) := by
  unfold Phi
  have hA0 : 0 ≤ eA t := (eA_pos t).le
  have hA1 : eA t ≤ 1 := eA_le_one ht
  have hLi : 0 ≤ ‖l‖⁻¹ := inv_nonneg.mpr (norm_nonneg _)
  have hk0 : 0 ≤ 2 * π * |k| := by positivity
  have hpi : 0 ≤ 4 * π ^ 2 / 2 := by positivity
  have e1 : 2 * π * |k| * (1 - eA t) ≤ 2 * π * |k| := by nlinarith
  have e2 : 4 * π ^ 2 / 2 * (1 - eA t * eA t) ≤ 4 * π ^ 2 / 2 := by nlinarith [mul_nonneg hA0 hA0]
  nlinarith [mul_le_mul_of_nonneg_left (add_le_add e1 e2) hLi]

private lemma Phi_ge (m₀ : ℝ) {t : ℝ} (ht : 0 ≤ t) : (2 * |l.re| + 2 * ‖l‖⁻¹ * m₀) * t ≤ Phi l k m₀ t := by
  unfold Phi
  have hA0 : 0 ≤ eA t := (eA_pos t).le
  have hA1 : eA t ≤ 1 := eA_le_one ht
  have hLi : 0 ≤ ‖l‖⁻¹ := inv_nonneg.mpr (norm_nonneg _)
  have hk0 : 0 ≤ 2 * π * |k| := by positivity
  have hpi : 0 ≤ 4 * π ^ 2 / 2 := by positivity
  have e1 : 0 ≤ 2 * π * |k| * (1 - eA t) := mul_nonneg hk0 (by linarith)
  have e2 : 0 ≤ 4 * π ^ 2 / 2 * (1 - eA t * eA t) := mul_nonneg hpi (by nlinarith)
  nlinarith [mul_nonneg hLi (add_nonneg e1 e2)]

include hf hf' hfeq in

private lemma Efun_le (hl : l ≠ 0) (m₀ : ℝ) (hm₀ : ‖ν ^ 2 - l ^ 2‖ ≤ m₀) (η : ℝ) (hη : 0 < η)
    (AF c : ℝ) (hAF : 0 ≤ AF) (hF : ∀ t : ℝ, 0 ≤ t → ‖Ff h t‖ ^ 2 ≤ AF * Real.exp (c * t)) {t : ℝ} (ht : 0 ≤ t) :
    Efun l f t ≤ Real.exp (Phi l k m₀ t + η * t) *
      (Efun l f 0 + 2 * η⁻¹ * AF / max (c - (2 * |l.re| + 2 * ‖l‖⁻¹ * m₀) - η) η *
        Real.exp (max (c - (2 * |l.re| + 2 * ‖l‖⁻¹ * m₀) - η) η * t)) := by
  set ρ : ℝ := 2 * |l.re| + 2 * ‖l‖⁻¹ * m₀ with hρdef
  set γ' : ℝ := max (c - ρ - η) η with hγ'def
  have hγ' : 0 < γ' := lt_of_lt_of_le hη (le_max_right _ _)
  set B : ℝ := 2 * η⁻¹ * AF with hBdef
  have hB : 0 ≤ B := by have := inv_nonneg.mpr hη.le; positivity

  set ψ : ℝ → ℝ := fun x => (Real.exp (γ' * x) - 1) / γ' with hψdef
  have hψ : ∀ x : ℝ, HasDerivAt ψ (Real.exp (γ' * x)) x := by
    intro x
    have h1 : HasDerivAt (fun y : ℝ => γ' * y) (γ' * 1) x := (hasDerivAt_id x).const_mul γ'
    have h2 : HasDerivAt (fun y : ℝ => Real.exp (γ' * y)) (Real.exp (γ' * x) * (γ' * 1)) x := h1.exp
    have h3 := (h2.sub_const 1).div_const γ'
    convert h3 using 1
    · rfl
    · rfl
    field_simp

  set Z : ℝ → ℝ := fun x => Efun l f x * Real.exp (-(Phi l k m₀ x + η * x)) - B * ψ x with hZdef
  have hZ : ∀ x : ℝ, ∃ Z' : ℝ, HasDerivAt Z Z' x ∧ (0 ≤ x → Z' ≤ 0) := by
    intro x
    obtain ⟨E', hE', hle⟩ := Efun_hasDerivAt_le ν l k f h hf hf' hfeq hl m₀ hm₀ η hη x
    have hPη : HasDerivAt (fun y => Phi l k m₀ y + η * y) (rate l k m₀ x + η * 1) x :=
      (Phi_hasDerivAt l k m₀ x).add ((hasDerivAt_id x).const_mul η)
    have hP : HasDerivAt (fun y => Real.exp (-(Phi l k m₀ y + η * y)))
        (Real.exp (-(Phi l k m₀ x + η * x)) * (-(rate l k m₀ x + η * 1))) x := hPη.neg.exp
    refine ⟨_, (hE'.mul hP).sub ((hψ x).const_mul B), fun hx => ?_⟩
    have hexp : 0 < Real.exp (-(Phi l k m₀ x + η * x)) := Real.exp_pos _
    have hE0 := Efun_nonneg l f x

    have hPhi : (ρ + η) * x ≤ Phi l k m₀ x + η * x := by
      have := Phi_ge l k m₀ hx; rw [← hρdef] at this; linarith
    have hIF : Real.exp (-(Phi l k m₀ x + η * x)) ≤ Real.exp (-((ρ + η) * x)) :=
      Real.exp_le_exp.mpr (by linarith)
    have hforce : 2 * η⁻¹ * ‖Ff h x‖ ^ 2 * Real.exp (-(Phi l k m₀ x + η * x)) ≤ B * Real.exp (γ' * x) := by
      have h1 : 2 * η⁻¹ * ‖Ff h x‖ ^ 2 ≤ B * Real.exp (c * x) := by
        rw [hBdef]
        have := mul_le_mul_of_nonneg_left (hF x hx) (by have := inv_nonneg.mpr hη.le; positivity : (0:ℝ) ≤ 2 * η⁻¹)
        linarith [this]
      have h2 : Real.exp (c * x) * Real.exp (-((ρ + η) * x)) ≤ Real.exp (γ' * x) := by
        rw [← Real.exp_add]
        refine Real.exp_le_exp.mpr ?_
        have : (c - ρ - η) * x ≤ γ' * x := mul_le_mul_of_nonneg_right (le_max_left _ _) hx
        linarith
      have h3 : 0 ≤ 2 * η⁻¹ * ‖Ff h x‖ ^ 2 := by have := inv_nonneg.mpr hη.le; positivity
      calc 2 * η⁻¹ * ‖Ff h x‖ ^ 2 * Real.exp (-(Phi l k m₀ x + η * x))
          ≤ 2 * η⁻¹ * ‖Ff h x‖ ^ 2 * Real.exp (-((ρ + η) * x)) := mul_le_mul_of_nonneg_left hIF h3
        _ ≤ B * Real.exp (c * x) * Real.exp (-((ρ + η) * x)) :=
            mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
        _ = B * (Real.exp (c * x) * Real.exp (-((ρ + η) * x))) := by ring
        _ ≤ B * Real.exp (γ' * x) := mul_le_mul_of_nonneg_left h2 hB
    have : E' * Real.exp (-(Phi l k m₀ x + η * x)) +
          Efun l f x * (Real.exp (-(Phi l k m₀ x + η * x)) * -(rate l k m₀ x + η * 1)) - B * Real.exp (γ' * x)
        = Real.exp (-(Phi l k m₀ x + η * x)) * (E' - (rate l k m₀ x + η) * Efun l f x) - B * Real.exp (γ' * x) := by
      ring
    rw [this]
    have h4 : Real.exp (-(Phi l k m₀ x + η * x)) * (E' - (rate l k m₀ x + η) * Efun l f x)
        ≤ Real.exp (-(Phi l k m₀ x + η * x)) * (2 * η⁻¹ * ‖Ff h x‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (by linarith) hexp.le
    nlinarith [h4, hforce]
  have hcont : ContinuousOn Z (Set.Ici 0) := fun x _ => ((hZ x).choose_spec.1.continuousAt).continuousWithinAt
  have hdiff : DifferentiableOn ℝ Z (interior (Set.Ici (0 : ℝ))) :=
    fun x _ => ((hZ x).choose_spec.1.differentiableAt).differentiableWithinAt
  have hderiv : ∀ x ∈ interior (Set.Ici (0 : ℝ)), deriv Z x ≤ 0 := by
    intro x hx
    rw [interior_Ici] at hx
    obtain ⟨Z', hZ', hle⟩ := hZ x
    rw [hZ'.deriv]; exact hle (le_of_lt hx)
  have hanti : AntitoneOn Z (Set.Ici 0) := antitoneOn_of_deriv_nonpos (convex_Ici 0) hcont hdiff hderiv
  have h0 : Z t ≤ Z 0 := hanti Set.self_mem_Ici ht ht
  have hψ0 : ψ 0 = 0 := by simp [hψdef]
  have hZ0 : Z 0 = Efun l f 0 := by
    simp only [hZdef, hψ0, Phi_zero, mul_zero, add_zero, neg_zero, Real.exp_zero, mul_one, sub_zero]
  rw [hZ0] at h0
  have hZt : Z t = Efun l f t * Real.exp (-(Phi l k m₀ t + η * t)) - B * ψ t := rfl
  rw [hZt] at h0

  have hψle : ψ t ≤ Real.exp (γ' * t) / γ' := by
    rw [hψdef]
    exact div_le_div_of_nonneg_right (by linarith [Real.exp_pos (γ' * t)]) hγ'.le
  have h1 : Efun l f t * Real.exp (-(Phi l k m₀ t + η * t)) ≤ Efun l f 0 + B / γ' * Real.exp (γ' * t) := by
    have := mul_le_mul_of_nonneg_left hψle hB
    have h' : B * (Real.exp (γ' * t) / γ') = B / γ' * Real.exp (γ' * t) := by ring
    linarith
  have hpos : 0 < Real.exp (Phi l k m₀ t + η * t) := Real.exp_pos _
  have h2 := mul_le_mul_of_nonneg_right h1 hpos.le
  rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one] at h2
  have hB' : B / γ' = 2 * η⁻¹ * AF / γ' := by rw [hBdef]
  rw [hB'] at h2
  linarith [h2]

include hf hf' hfeq in

private theorem engine (hl : l ≠ 0) (m₀ : ℝ) (hm₀ : ‖ν ^ 2 - l ^ 2‖ ≤ m₀) (η : ℝ) (hη : 0 < η)
    (AF c : ℝ) (hAF : 0 ≤ AF) (hF : ∀ t : ℝ, 0 ≤ t → ‖Ff h t‖ ^ 2 ≤ AF * Real.exp (c * t)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 0 < y → y ≤ 1 →
      ‖f y‖ ≤ C * y ^ ((1 - ((2 * |l.re| + 2 * ‖l‖⁻¹ * m₀) + η +
        max (c - (2 * |l.re| + 2 * ‖l‖⁻¹ * m₀) - η) η)) / 2) := by
  set ρ : ℝ := 2 * |l.re| + 2 * ‖l‖⁻¹ * m₀ with hρdef
  set γ' : ℝ := max (c - ρ - η) η with hγ'def
  have hγ' : 0 < γ' := lt_of_lt_of_le hη (le_max_right _ _)
  set ρ' : ℝ := ρ + η + γ' with hρ'def
  set K : ℝ := 2 * ‖l‖⁻¹ * (2 * π * |k| + 4 * π ^ 2 / 2) with hKdef
  have hLi : 0 ≤ ‖l‖⁻¹ := inv_nonneg.mpr (norm_nonneg _)
  set D : ℝ := Efun l f 0 + 2 * η⁻¹ * AF / γ' with hDdef
  have hD : 0 ≤ D := by
    have := Efun_nonneg l f 0; have := inv_nonneg.mpr hη.le; positivity
  set Cst : ℝ := ‖l‖⁻¹ * ‖l‖⁻¹ / 2 * (D * Real.exp K) with hCst
  have hCst0 : 0 ≤ Cst := by have := Real.exp_pos K; positivity
  clear_value Cst D K ρ' γ' ρ
  refine ⟨Real.sqrt Cst, Real.sqrt_nonneg _, ?_⟩
  intro y hy hy1

  set t : ℝ := -Real.log y with htdef
  have ht : 0 ≤ t := by have := Real.log_nonpos hy.le hy1; linarith
  have hAt : eA t = y := by unfold eA; rw [htdef, neg_neg, Real.exp_log hy]

  have hG : Gf f t = ((eB t : ℝ) : ℂ) * f y := by unfold Gf; rw [hAt]
  have hGn : ‖Gf f t‖ = eB t * ‖f y‖ := by
    rw [hG, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (eB_pos t)]
  have hfy_sq : ‖f y‖ ^ 2 = y * ‖Gf f t‖ ^ 2 := by
    rw [hGn, mul_pow, ← hAt, ← mul_assoc, eA_mul_eB_sq, one_mul]

  have hE := Efun_le ν l k f h hf hf' hfeq hl m₀ hm₀ η hη AF c hAF hF ht
  rw [← hρdef, ← hγ'def] at hE
  have hgl : 2 * ‖Gf f t‖ ≤ ‖l‖⁻¹ * (‖vp l f t‖ + ‖vm l f t‖) := by
    have h1 : ‖vp l f t - vm l f t‖ ≤ ‖vp l f t‖ + ‖vm l f t‖ := norm_sub_le _ _
    rw [vp_sub_vm, norm_mul, norm_mul] at h1
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    rw [h2] at h1
    have h3 := mul_le_mul_of_nonneg_left h1 hLi
    have hl0 : 0 < ‖l‖ := norm_pos_iff.mpr hl
    calc 2 * ‖Gf f t‖ = ‖l‖⁻¹ * (2 * ‖l‖ * ‖Gf f t‖) := by field_simp
      _ ≤ ‖l‖⁻¹ * (‖vp l f t‖ + ‖vm l f t‖) := h3
  have hEt : Efun l f t = ‖vp l f t‖ ^ 2 + ‖vm l f t‖ ^ 2 := by unfold Efun; rw [nsq_eq, nsq_eq]
  have hGsq : ‖Gf f t‖ ^ 2 ≤ ‖l‖⁻¹ * ‖l‖⁻¹ / 2 * Efun l f t := by
    rw [hEt]
    have hp := norm_nonneg (vp l f t); have hq := norm_nonneg (vm l f t); have hg0 := norm_nonneg (Gf f t)
    have hsum : (‖vp l f t‖ + ‖vm l f t‖) ^ 2 ≤ 2 * (‖vp l f t‖ ^ 2 + ‖vm l f t‖ ^ 2) := by
      nlinarith [sq_nonneg (‖vp l f t‖ - ‖vm l f t‖)]
    have h4 : (2 * ‖Gf f t‖) ^ 2 ≤ (‖l‖⁻¹ * (‖vp l f t‖ + ‖vm l f t‖)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hgl 2
    have hLi2 : 0 ≤ ‖l‖⁻¹ * ‖l‖⁻¹ := mul_nonneg hLi hLi
    nlinarith [mul_le_mul_of_nonneg_left hsum hLi2]

  have hPhi := Phi_le l k m₀ ht
  rw [← hρdef] at hPhi
  have hexp1 : Real.exp (Phi l k m₀ t + η * t) ≤ Real.exp K * Real.exp ((ρ + η) * t) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by rw [hKdef]; linarith)
  have hexp2 : Efun l f 0 + 2 * η⁻¹ * AF / γ' * Real.exp (γ' * t) ≤ D * Real.exp (γ' * t) := by
    rw [hDdef, add_mul]
    have h1 : 1 ≤ Real.exp (γ' * t) := Real.one_le_exp (mul_nonneg hγ'.le ht)
    have h0 := Efun_nonneg l f 0
    nlinarith
  have hEy : Efun l f t ≤ D * Real.exp K * y ^ (-ρ') := by
    have hyρ : y ^ (-ρ') = Real.exp ((ρ + η) * t) * Real.exp (γ' * t) := by
      rw [Real.rpow_def_of_pos hy, ← Real.exp_add]
      congr 1
      rw [htdef, hρ'def]; ring
    rw [hyρ]
    have hE0 : 0 ≤ Efun l f 0 + 2 * η⁻¹ * AF / γ' * Real.exp (γ' * t) := by
      have := Efun_nonneg l f 0; have := inv_nonneg.mpr hη.le; have := Real.exp_pos (γ' * t); positivity
    calc Efun l f t ≤ Real.exp (Phi l k m₀ t + η * t) * (Efun l f 0 + 2 * η⁻¹ * AF / γ' * Real.exp (γ' * t)) := hE
      _ ≤ (Real.exp K * Real.exp ((ρ + η) * t)) * (D * Real.exp (γ' * t)) :=
          mul_le_mul hexp1 hexp2 hE0 (by positivity)
      _ = D * Real.exp K * (Real.exp ((ρ + η) * t) * Real.exp (γ' * t)) := by ring

  have hsq : ‖f y‖ ^ 2 ≤ Cst * (y * y ^ (-ρ')) := by
    have hLi2 : 0 ≤ ‖l‖⁻¹ * ‖l‖⁻¹ / 2 := by positivity
    rw [hCst]
    exact sq_assemble hy.le hLi2 hfy_sq hGsq hEy
  have hyρ : y * y ^ (-ρ') = (y ^ ((1 - ρ') / 2)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hy.le]
    have h1 : y * y ^ (-ρ') = y ^ (1 + -ρ') := by rw [Real.rpow_add hy, Real.rpow_one]
    rw [h1]
    congr 1; push_cast; ring
  rw [hyρ] at hsq
  have hrhs : 0 ≤ Real.sqrt Cst * y ^ ((1 - ρ') / 2) := by positivity
  have hsq' : ‖f y‖ ^ 2 ≤ (Real.sqrt Cst * y ^ ((1 - ρ') / 2)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hCst0]; exact hsq
  have := abs_le_of_sq_le_sq hsq' hrhs
  rwa [abs_of_nonneg (norm_nonneg _)] at this

end energy

end GluePNearZero41F

open GluePNearZero41F in

theorem solution
    (ν : ℂ) (k σ A : ℝ) (f h : ℝ → ℂ)
    (hf : DifferentiableOn ℝ f (Set.Ioi 0)) (hf' : DifferentiableOn ℝ (deriv f) (Set.Ioi 0))
    (hh : ∀ y : ℝ, 0 < y → y ≤ 1 → ‖h y‖ ≤ A * y ^ σ)
    (hfeq : ∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv f) y
            + (1 / 4 - ν ^ 2 + 2 * (π : ℂ) * (k : ℂ) * (y : ℂ) - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2) * f y = h y) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 → ‖f y‖ ≤ C * y ^ (min (1 / 2 - |ν.re|) σ - ε) := by
  intro ε hε

  have hF : ∀ t : ℝ, 0 ≤ t → ‖Ff h t‖ ^ 2 ≤ A ^ 2 * Real.exp ((1 - 2 * σ) * t) := by
    intro t ht
    have hy : 0 < eA t := eA_pos t
    have hy1 : eA t ≤ 1 := eA_le_one ht
    have hb : ‖Ff h t‖ ≤ eB t * (A * eA t ^ σ) := by
      unfold Ff
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (eB_pos t)]
      exact mul_le_mul_of_nonneg_left (hh (eA t) hy hy1) (eB_pos t).le
    have hb0 : 0 ≤ eB t * (A * eA t ^ σ) := (norm_nonneg _).trans hb
    have hsq : ‖Ff h t‖ ^ 2 ≤ (eB t * (A * eA t ^ σ)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
    have heq : (eB t * (A * eA t ^ σ)) ^ 2 = A ^ 2 * Real.exp ((1 - 2 * σ) * t) := by
      have h1 : (eA t ^ σ) ^ 2 = Real.exp (-(2 * σ * t)) := by
        unfold eA
        rw [← Real.exp_mul, ← Real.exp_nat_mul]; congr 1; push_cast; ring
      have h2 : Real.exp ((1 - 2 * σ) * t) = Real.exp t * Real.exp (-(2 * σ * t)) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [mul_pow, mul_pow, eB_sq, h1, h2]; ring
    rw [← heq]; exact hsq
  have hA2 : 0 ≤ A ^ 2 := sq_nonneg A

  have hmono : ∀ {C e : ℝ}, 0 ≤ C → min (1 / 2 - |ν.re|) σ - ε ≤ e →
      ∀ y : ℝ, 0 < y → y ≤ 1 → ‖f y‖ ≤ C * y ^ e → ‖f y‖ ≤ C * y ^ (min (1 / 2 - |ν.re|) σ - ε) := by
    intro C e hC he y hy hy1 hfy
    exact hfy.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hy hy1 he) hC)
  have hmin1 : min (1 / 2 - |ν.re|) σ ≤ 1 / 2 - |ν.re| := min_le_left _ _
  have hmin2 : min (1 / 2 - |ν.re|) σ ≤ σ := min_le_right _ _
  by_cases hν : ν = 0
  ·
    subst hν
    have hε4 : (0 : ℝ) < ε / 4 := by positivity
    have hl : (((ε / 4 : ℝ) : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr hε4.ne'
    have hnorm : ‖(((ε / 4 : ℝ) : ℂ))‖ = ε / 4 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε4]
    have hm : ‖(0 : ℂ) ^ 2 - (((ε / 4 : ℝ) : ℂ)) ^ 2‖ ≤ (ε / 4) ^ 2 := by
      rw [show (0 : ℂ) ^ 2 - (((ε / 4 : ℝ) : ℂ)) ^ 2 = -((((ε / 4 : ℝ) : ℂ)) ^ 2) by ring, norm_neg, norm_pow,
        hnorm]
    have hη : (0 : ℝ) < ε / 2 := by positivity
    obtain ⟨C, hC0, hC⟩ :=
      engine 0 (((ε / 4 : ℝ) : ℂ)) k f h hf hf' hfeq hl ((ε / 4) ^ 2) hm (ε / 2) hη (A ^ 2) (1 - 2 * σ) hA2 hF
    refine ⟨C, fun y hy hy1 => hmono hC0 ?_ y hy hy1 (hC y hy hy1)⟩
    have hρ : 2 * |(((ε / 4 : ℝ) : ℂ)).re| + 2 * ‖(((ε / 4 : ℝ) : ℂ))‖⁻¹ * (ε / 4) ^ 2 = ε := by
      rw [hnorm, Complex.ofReal_re, abs_of_pos hε4]
      field_simp
      ring
    rw [hρ, Complex.zero_re, abs_zero, sub_zero]
    rw [Complex.zero_re, abs_zero, sub_zero] at hmin1 hmin2
    rcases le_total (1 - 2 * σ - ε - ε / 2) (ε / 2) with hc | hc
    · rw [max_eq_right hc]; linarith
    · rw [max_eq_left hc]; linarith
  ·
    have hm : ‖ν ^ 2 - ν ^ 2‖ ≤ 0 := by simp
    obtain ⟨C, hC0, hC⟩ := engine ν ν k f h hf hf' hfeq hν 0 hm ε hε (A ^ 2) (1 - 2 * σ) hA2 hF
    refine ⟨C, fun y hy hy1 => hmono hC0 ?_ y hy hy1 (hC y hy hy1)⟩
    rw [mul_zero, add_zero]
    rcases le_total (1 - 2 * σ - 2 * |ν.re| - ε) ε with hc | hc
    · rw [max_eq_right hc]; linarith
    · rw [max_eq_left hc]; linarith

end S_LanglandsTunnell_norm_le_mul_rpow_near_zero_of_whittaker_ode_of_forcing
end P2MW
export P2MW.S_LanglandsTunnell_norm_le_mul_rpow_near_zero_of_whittaker_ode_of_forcing (solution)
