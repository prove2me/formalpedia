-- Prove2me | solution 1 for LanglandsTunnell.Converse.exists_archDatumC_W_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/c1ef1d82-6eae-5f5f-8c55-3b0db25c0151

import Definitions.Def_LanglandsTunnell_ArchPlace
import Definitions.Def_LanglandsTunnell_JLConverse
import Theorems.Thm_LanglandsTunnell_TateLocal_localZeta_fourier_mul_symm
import Theorems.Thm_LanglandsTunnell_TateLocal_complexZeta_eq_localZeta
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_complex_eq_nnnorm_sq
import Theorems.Thm_LanglandsTunnell_ArchPlace_tateFourier_complexTestFun_zero_self
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_Converse_exists_archDatumC_W_ne_zero

set_option autoImplicit false

section

open Complex MeasureTheory FourierTransform

noncomputable section

namespace TateReal

private def sgnPow (a : ZMod 2) (w : ℝ) : ℂ := if a = 0 then 1 else ((SignType.sign w : ℝ) : ℂ)

private def gaussPoly (p : Polynomial ℂ) (α : ℝ) (β : ℂ) (w : ℝ) : ℂ :=
  p.eval (w : ℂ) * cexp (-Real.pi * α * (w : ℂ) ^ 2 + 2 * Real.pi * β * w)

private def IsGaussPoly (f : ℝ → ℂ) : Prop := ∃ (p : Polynomial ℂ) (α : ℝ) (β : ℂ), 0 < α ∧ f = gaussPoly p α β

private theorem fourier_const_mul (c : ℂ) (f : ℝ → ℂ) :
    (𝓕 fun x : ℝ => c * f x) = fun w : ℝ => c * 𝓕 f w := by
  funext w
  simp only [Real.fourier_real_eq_integral_exp_smul, smul_eq_mul]
  have hv : ∀ v : ℝ, cexp (((-2 * Real.pi * v * w : ℝ) : ℂ) * I) * (c * f v)
      = c * (cexp (((-2 * Real.pi * v * w : ℝ) : ℂ) * I) * f v) := fun v => by ring
  simp_rw [hv]
  exact MeasureTheory.integral_const_mul _ _

private theorem norm_sgnPow (a : ZMod 2) {w : ℝ} (hw : w ≠ 0) : ‖sgnPow a w‖ = 1 := by
  unfold sgnPow
  by_cases ha : a = 0
  · simp [ha]
  · rcases hw.lt_or_gt with h | h
    · simp [ha, sign_neg h]
    · simp [ha, sign_pos h]

private theorem measurable_sgnPow (a : ZMod 2) : Measurable (sgnPow a) := by
  have hcast : Monotone fun t : SignType => (t : ℝ) := by
    intro x y hxy
    cases x <;> cases y <;> simp_all
  unfold sgnPow
  by_cases ha : a = 0
  · simp only [ha, if_true]; exact measurable_const
  · simp only [ha, if_false]
    exact Complex.measurable_ofReal.comp (hcast.comp SignType.sign.monotone).measurable

private theorem integrable_comp_abs_of_integrableOn {g : ℝ → ℝ} (hg : IntegrableOn g (Set.Ioi 0)) :
    Integrable (fun x : ℝ => g |x|) := by
  have hpos : IntegrableOn (fun x : ℝ => g |x|) (Set.Ioi 0) :=
    (integrableOn_congr_fun (fun x hx => by rw [abs_eq_self.mpr (le_of_lt (by exact hx))])
      measurableSet_Ioi).mpr hg
  have hneg : IntegrableOn (fun x : ℝ => g |x|) (Set.Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let m : MeasurableEmbedding fun x : ℝ => -x := (Homeomorph.neg ℝ).measurableEmbedding
    rw [m.integrableOn_map_iff]
    simp_rw [Function.comp_def, abs_neg, Set.neg_preimage, Set.neg_Iic, neg_zero]
    exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hpos
  have := hneg.union hpos
  rwa [Set.Iic_union_Ioi, integrableOn_univ] at this

private theorem integrable_abs_rpow_mul_exp {b t : ℝ} (hb : 0 < b) (ht : -1 < t) :
    Integrable (fun x : ℝ => |x| ^ t * Real.exp (-b * x ^ 2)) := by
  have h := integrable_comp_abs_of_integrableOn (integrableOn_rpow_mul_exp_neg_mul_sq hb ht)
  simpa only [sq_abs] using h

private theorem integrable_monomial_term (n : ℕ) {α : ℝ} (hα : 0 < α) (β : ℂ) (a : ZMod 2) {s : ℂ} (hs : 0 < s.re) :
    Integrable (fun w : ℝ => ((w : ℂ) ^ n * cexp (-Real.pi * α * (w : ℂ) ^ 2 + 2 * Real.pi * β * w)) *
      sgnPow a w * ((|w| : ℝ) : ℂ) ^ (s - 1)) := by
  set b : ℝ := β.re with hb

  have hdom : Integrable (fun w : ℝ =>
      Real.exp (2 * Real.pi * b ^ 2 / α) * (|w| ^ ((n : ℝ) + (s.re - 1)) * Real.exp (-(Real.pi * α / 2) * w ^ 2))) :=
    (integrable_abs_rpow_mul_exp (by positivity) (by have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith)).const_mul _
  refine hdom.mono' ?_ ?_
  ·
    have h1 : Continuous fun w : ℝ => (w : ℂ) ^ n * cexp (-Real.pi * α * (w : ℂ) ^ 2 + 2 * Real.pi * β * w) :=
      (Complex.continuous_ofReal.pow n).mul (Complex.continuous_exp.comp
        ((continuous_const.mul (Complex.continuous_ofReal.pow 2)).add
          (continuous_const.mul Complex.continuous_ofReal)))
    have h2 : Measurable fun w : ℝ => sgnPow a w := measurable_sgnPow a
    have h3 : Measurable fun w : ℝ => ((|w| : ℝ) : ℂ) ^ (s - 1) :=
      (Complex.measurable_ofReal.comp measurable_abs).pow_const _
    exact ((h1.measurable.mul h2).mul h3).aestronglyMeasurable
  ·
    filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ))] with w hw
    have hw0 : w ≠ 0 := hw
    have habs : 0 < |w| := abs_pos.mpr hw0
    have hre : (-Real.pi * α * (w : ℂ) ^ 2 + 2 * Real.pi * β * w).re = -Real.pi * α * w ^ 2 + 2 * Real.pi * b * w := by
      simp [hb, sq]
    rw [norm_mul, norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp, hre,
      norm_sgnPow a hw0, mul_one, norm_cpow_eq_rpow_re_of_pos habs, Complex.sub_re, Complex.one_re]
    have hkey : -Real.pi * α * w ^ 2 + 2 * Real.pi * b * w ≤ 2 * Real.pi * b ^ 2 / α + -(Real.pi * α / 2) * w ^ 2 := by
      have h0 : 0 ≤ Real.pi * α / 2 * (w - 2 * b / α) ^ 2 := by positivity
      have hexp : Real.pi * α / 2 * (w - 2 * b / α) ^ 2
          = Real.pi * α / 2 * w ^ 2 - 2 * Real.pi * b * w + 2 * Real.pi * b ^ 2 / α := by
        field_simp; ring
      linarith
    calc |w| ^ n * Real.exp (-Real.pi * α * w ^ 2 + 2 * Real.pi * b * w) * |w| ^ (s.re - 1)
        = |w| ^ ((n : ℝ) + (s.re - 1)) * Real.exp (-Real.pi * α * w ^ 2 + 2 * Real.pi * b * w) := by
          rw [Real.rpow_add habs, Real.rpow_natCast]; ring
      _ ≤ |w| ^ ((n : ℝ) + (s.re - 1)) * Real.exp (2 * Real.pi * b ^ 2 / α + -(Real.pi * α / 2) * w ^ 2) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hkey) (by positivity)
      _ = Real.exp (2 * Real.pi * b ^ 2 / α) *
            (|w| ^ ((n : ℝ) + (s.re - 1)) * Real.exp (-(Real.pi * α / 2) * w ^ 2)) := by
          rw [Real.exp_add]; ring

private theorem IsGaussPoly.integrable_tate {f : ℝ → ℂ} (hf : IsGaussPoly f) (a : ZMod 2) {s : ℂ} (hs : 0 < s.re) :
    Integrable (fun w : ℝ => f w * sgnPow a w * ((|w| : ℝ) : ℂ) ^ (s - 1)) := by
  obtain ⟨p, α, β, hα, rfl⟩ := hf
  have hfun : (fun w : ℝ => gaussPoly p α β w * sgnPow a w * ((|w| : ℝ) : ℂ) ^ (s - 1))
      = fun w : ℝ => ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i *
          (((w : ℂ) ^ i * cexp (-Real.pi * α * (w : ℂ) ^ 2 + 2 * Real.pi * β * w)) * sgnPow a w *
            ((|w| : ℝ) : ℂ) ^ (s - 1)) := by
    funext w
    unfold gaussPoly
    rw [Polynomial.eval_eq_sum_range, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [hfun]

  induction Finset.range (p.natDegree + 1) using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact integrable_zero _ _ _
  | @insert j t hj ih =>
    simp only [Finset.sum_insert hj]
    exact ((integrable_monomial_term j hα β a hs).const_mul _).add ih

private theorem IsGaussPoly.integrable {f : ℝ → ℂ} (hf : IsGaussPoly f) : Integrable f := by
  have h := hf.integrable_tate 0 (s := 1) (by simp)
  simpa [sgnPow] using h

private theorem fourier_add' {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) : 𝓕 (f + g) = 𝓕 f + 𝓕 g :=
  VectorFourier.fourierIntegral_add Real.continuous_fourierChar continuous_inner hf hg

private theorem gaussPoly_add (p q : Polynomial ℂ) (α : ℝ) (β : ℂ) :
    gaussPoly (p + q) α β = gaussPoly p α β + gaussPoly q α β := by
  funext w; simp only [gaussPoly, Polynomial.eval_add, Pi.add_apply]; ring

private theorem gaussPoly_C_mul (c : ℂ) (p : Polynomial ℂ) (α : ℝ) (β : ℂ) (w : ℝ) :
    gaussPoly (Polynomial.C c * p) α β w = c * gaussPoly p α β w := by
  simp only [gaussPoly, Polynomial.eval_mul, Polynomial.eval_C]; ring

private theorem gaussPoly_X_mul (p : Polynomial ℂ) (α : ℝ) (β : ℂ) (w : ℝ) :
    gaussPoly (Polynomial.X * p) α β w = (w : ℂ) * gaussPoly p α β w := by
  simp only [gaussPoly, Polynomial.eval_mul, Polynomial.eval_X]; ring

private theorem
    isGaussPoly_gaussPoly (p : Polynomial ℂ) {α : ℝ} (hα : 0 < α) (β : ℂ) : IsGaussPoly (gaussPoly p α β) :=
  ⟨p, α, β, hα, rfl⟩

private theorem deriv_gaussPoly (p : Polynomial ℂ) (α : ℝ) (β : ℂ) :
    deriv (gaussPoly p α β) = gaussPoly (Polynomial.derivative p +
      p * (Polynomial.C ((-2 * Real.pi * α : ℝ) : ℂ) * Polynomial.X + Polynomial.C (2 * Real.pi * β))) α β := by
  funext w
  have h1 : HasDerivAt (fun w : ℝ => p.eval (w : ℂ)) (p.derivative.eval (w : ℂ)) w :=
    (Polynomial.hasDerivAt p (w : ℂ)).comp_ofReal
  have h2 : HasDerivAt (fun w : ℝ => cexp (-Real.pi * α * (w : ℂ) ^ 2 + 2 * Real.pi * β * w))
      (cexp (-Real.pi * α * (w : ℂ) ^ 2 + 2 * Real.pi * β * w) *
        (-Real.pi * α * (2 * (w : ℂ)) + 2 * Real.pi * β)) w := by
    have hq : HasDerivAt (fun w : ℝ => (-Real.pi * α * (w : ℂ) ^ 2 + 2 * Real.pi * β * w))
        (-Real.pi * α * (2 * (w : ℂ)) + 2 * Real.pi * β) w := by
      have ha := ((hasDerivAt_id w).ofReal_comp.fun_pow 2).const_mul (-(Real.pi : ℂ) * α)
      have hb := (hasDerivAt_id w).ofReal_comp.const_mul (2 * (Real.pi : ℂ) * β)
      have hab := ha.fun_add hb
      first | simpa [pow_one] using hab | (have h' := hab; simp [pow_one] at h'; exact h') | exact hab
    exact hq.cexp
  have h : HasDerivAt (gaussPoly p α β) _ w := h1.mul h2
  rw [h.deriv]
  simp only [gaussPoly, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  push_cast
  ring

private theorem fourier_gaussPoly (p : Polynomial ℂ) {α : ℝ} (hα : 0 < α) (β : ℂ) :
    ∃ q : Polynomial ℂ, 𝓕 (gaussPoly p α β) = gaussPoly q (1 / α) (-I * β / α) := by
  have hα' : (α : ℂ) ≠ 0 := by exact_mod_cast hα.ne'
  have hα1 : 0 < 1 / α := by positivity
  induction p using Polynomial.induction_on with
  | C c =>
    refine ⟨Polynomial.C (c * (1 / (α : ℂ) ^ (1 / 2 : ℂ)) * cexp (Real.pi * β ^ 2 / α)), ?_⟩
    have hbase := fourier_gaussian_pi' (b := (α : ℂ)) (by simpa using hα) β
    have hfun : gaussPoly (Polynomial.C c) α β
        = fun x : ℝ => c * cexp (-Real.pi * (α : ℂ) * x ^ 2 + 2 * Real.pi * β * x) := by
      funext x; simp [gaussPoly]
    rw [hfun, fourier_const_mul, hbase]
    funext t
    simp only [gaussPoly, Polynomial.eval_C]
    have hE : -(Real.pi : ℂ) / α * ((t : ℂ) + I * β) ^ 2
        = Real.pi * β ^ 2 / α + (-Real.pi * ((1 / α : ℝ) : ℂ) * (t : ℂ) ^ 2 + 2 * Real.pi * (-I * β / α) * t) := by
      push_cast
      linear_combination (-((Real.pi : ℂ) * β ^ 2 / α)) * Complex.I_sq
    rw [hE, Complex.exp_add]
    ring
  | add p q hp hq =>
    obtain ⟨p', hp'⟩ := hp
    obtain ⟨q', hq'⟩ := hq
    refine ⟨p' + q', ?_⟩
    rw [gaussPoly_add, fourier_add' (isGaussPoly_gaussPoly p hα β).integrable
      (isGaussPoly_gaussPoly q hα β).integrable, hp', hq', gaussPoly_add]
  | monomial n c ih =>
    obtain ⟨q, hq⟩ := ih

    obtain ⟨F, hF⟩ : ∃ F : ℝ → ℂ, F = gaussPoly (Polynomial.C c * Polynomial.X ^ n) α β := ⟨_, rfl⟩
    rw [← hF] at hq
    have hpoly : Polynomial.C c * Polynomial.X ^ (n + 1)
        = Polynomial.X * (Polynomial.C c * Polynomial.X ^ n) := by ring
    have hfun : gaussPoly (Polynomial.C c * Polynomial.X ^ (n + 1)) α β = fun x : ℝ => (x : ℂ) * F x := by
      funext x; rw [hpoly, gaussPoly_X_mul, hF]
    have hFint : Integrable F := by rw [hF]; exact (isGaussPoly_gaussPoly _ hα β).integrable
    have hxF : Integrable (fun x : ℝ => x • F x) := by
      have := (isGaussPoly_gaussPoly (Polynomial.X * (Polynomial.C c * Polynomial.X ^ n)) hα β).integrable
      refine this.congr (Filter.Eventually.of_forall fun x => ?_)
      simp only [gaussPoly_X_mul, Complex.real_smul, hF]
    have hd := Real.deriv_fourier hFint hxF
    have hlin : (fun x : ℝ => (-2 * Real.pi * I * x) • F x) = fun x : ℝ => (-2 * Real.pi * I) * ((x : ℂ) * F x) := by
      funext x; simp only [smul_eq_mul]; ring
    rw [hlin, fourier_const_mul, hq, deriv_gaussPoly] at hd

    obtain ⟨Q, hQ⟩ : ∃ Q : Polynomial ℂ, gaussPoly Q (1 / α) (-I * β / α)
        = fun w : ℝ => (-2 * Real.pi * I) * 𝓕 (fun x : ℝ => (x : ℂ) * F x) w := ⟨_, hd⟩
    refine ⟨Polynomial.C (1 / (-2 * Real.pi * I)) * Q, ?_⟩
    rw [hfun]
    funext t
    have ht := congrFun hQ t
    rw [gaussPoly_C_mul, ht]
    have h2pi : (-2 * (Real.pi : ℂ) * I) ≠ 0 := by simp [Real.pi_ne_zero]
    field_simp

end TateReal

namespace TateReal

open LanglandsTunnell.TateLocal LanglandsTunnell.ArchPlace
open scoped ENNReal

namespace W3

private theorem exists_pd_lower {α₁ α₂ γr : ℝ} (h₁ : 0 < α₁) (h₂ : 0 < α₂) (hpd : γr ^ 2 < α₁ * α₂) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ x t : ℝ, lam * (x ^ 2 + t ^ 2) ≤ α₁ * x ^ 2 + α₂ * t ^ 2 - 2 * γr * x * t := by
  set lam : ℝ := min (min α₁ α₂) ((α₁ * α₂ - γr ^ 2) / (α₁ + α₂)) / 2 with hlam
  have hsum : 0 < α₁ + α₂ := by linarith
  have hq : 0 < (α₁ * α₂ - γr ^ 2) / (α₁ + α₂) := div_pos (by linarith) hsum
  have hlam0 : 0 < lam := by rw [hlam]; positivity
  have hmin1 := min_le_left (min α₁ α₂) ((α₁ * α₂ - γr ^ 2) / (α₁ + α₂))
  have hmin2 := min_le_right (min α₁ α₂) ((α₁ * α₂ - γr ^ 2) / (α₁ + α₂))
  have hl1 : lam < α₁ := by
    have : lam ≤ min α₁ α₂ / 2 := by rw [hlam]; linarith
    linarith [min_le_left α₁ α₂, hlam0, h₁]
  have hl2 : lam < α₂ := by
    have : lam ≤ min α₁ α₂ / 2 := by rw [hlam]; linarith
    linarith [min_le_right α₁ α₂, hlam0, h₂]
  have hl3 : lam * (α₁ + α₂) ≤ (α₁ * α₂ - γr ^ 2) / 2 := by
    have : lam ≤ (α₁ * α₂ - γr ^ 2) / (α₁ + α₂) / 2 := by rw [hlam]; linarith
    calc lam * (α₁ + α₂) ≤ (α₁ * α₂ - γr ^ 2) / (α₁ + α₂) / 2 * (α₁ + α₂) := by gcongr
      _ = (α₁ * α₂ - γr ^ 2) / 2 := by field_simp

  have hac : γr ^ 2 ≤ (α₁ - lam) * (α₂ - lam) := by nlinarith [hl3, hlam0, hpd]
  refine ⟨lam, hlam0, fun x t => ?_⟩
  have ha : 0 < α₁ - lam := by linarith

  have key : 0 ≤ (α₁ - lam) * ((α₁ - lam) * x ^ 2 + (α₂ - lam) * t ^ 2 - 2 * γr * x * t) := by
    have e : (α₁ - lam) * ((α₁ - lam) * x ^ 2 + (α₂ - lam) * t ^ 2 - 2 * γr * x * t)
        = ((α₁ - lam) * x - γr * t) ^ 2 + ((α₁ - lam) * (α₂ - lam) - γr ^ 2) * t ^ 2 := by ring
    rw [e]
    have : 0 ≤ ((α₁ - lam) * (α₂ - lam) - γr ^ 2) * t ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
    positivity
  have : 0 ≤ (α₁ - lam) * x ^ 2 + (α₂ - lam) * t ^ 2 - 2 * γr * x * t := (mul_nonneg_iff_of_pos_left ha).mp key
  nlinarith [this]

end W3

namespace W3

open Real

private theorem norm_Gamma_le_Gamma_re {v : ℂ} (hv : 0 < v.re) : ‖Complex.Gamma v‖ ≤ Real.Gamma v.re := by
  rw [Complex.Gamma_eq_integral hv, Real.Gamma_eq_integral hv, Complex.GammaIntegral]
  refine (MeasureTheory.norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have hx' : (0 : ℝ) < x := hx
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx', Complex.sub_re, Complex.one_re]
  simp [Complex.norm_exp]

private theorem norm_sin_le_exp_abs_im (w : ℂ) : ‖Complex.sin w‖ ≤ Real.exp |w.im| := by
  rw [Complex.sin]
  have h1 : ‖Complex.exp (-w * I)‖ = Real.exp w.im := by
    rw [Complex.norm_exp]; congr 1; simp
  have h2 : ‖Complex.exp (w * I)‖ = Real.exp (-w.im) := by
    rw [Complex.norm_exp]; congr 1; simp
  calc ‖(Complex.exp (-w * I) - Complex.exp (w * I)) * I / 2‖
      = ‖Complex.exp (-w * I) - Complex.exp (w * I)‖ / 2 := by
        rw [norm_div, norm_mul, Complex.norm_I, mul_one]; simp
    _ ≤ (Real.exp w.im + Real.exp (-w.im)) / 2 := by
        gcongr
        calc ‖Complex.exp (-w * I) - Complex.exp (w * I)‖
            ≤ ‖Complex.exp (-w * I)‖ + ‖Complex.exp (w * I)‖ := norm_sub_le _ _
          _ = Real.exp w.im + Real.exp (-w.im) := by rw [h1, h2]
    _ ≤ (Real.exp |w.im| + Real.exp |w.im|) / 2 := by
        gcongr
        · exact le_abs_self _
        · exact neg_le_abs _
    _ = Real.exp |w.im| := by ring

private theorem inv_Gamma_eq_prod_mul (z : ℂ) (n : ℕ) :
    (Complex.Gamma z)⁻¹ = (∏ k ∈ Finset.range n, (z + k)) * (Complex.Gamma (z + n))⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ih, Finset.prod_range_succ, Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (z + n)]
    push_cast
    ring_nf

private theorem norm_Gamma_le_norm_Gamma_add {v : ℂ} (hv : 1 ≤ |v.im|) (m : ℕ) :
    ‖Complex.Gamma v‖ ≤ ‖Complex.Gamma (v + m)‖ := by
  have him : v.im ≠ 0 := fun h => by rw [h, abs_zero] at hv; linarith
  have hv0 : Complex.Gamma v ≠ 0 := Complex.Gamma_ne_zero fun k hk => him (by rw [hk]; simp)
  have hprod : 1 ≤ ‖∏ k ∈ Finset.range m, (v + k)‖ := by
    rw [norm_prod]
    calc (1 : ℝ) = ∏ _k ∈ Finset.range m, (1 : ℝ) := by simp
      _ ≤ ∏ k ∈ Finset.range m, ‖v + (k : ℂ)‖ := by
          refine Finset.prod_le_prod (fun _ _ => zero_le_one) fun k _ => ?_
          calc (1 : ℝ) ≤ |v.im| := hv
            _ = |(v + k).im| := by simp
            _ ≤ ‖v + k‖ := Complex.abs_im_le_norm _
  have h := inv_Gamma_eq_prod_mul v m
  have hnorm : ‖Complex.Gamma v‖⁻¹ = ‖∏ k ∈ Finset.range m, (v + k)‖ * ‖Complex.Gamma (v + m)‖⁻¹ := by
    rw [← norm_inv, h, norm_mul, norm_inv]
  have hpos : 0 < ‖Complex.Gamma v‖ := norm_pos_iff.mpr hv0
  have hG : 0 ≤ ‖Complex.Gamma (v + m)‖ := norm_nonneg _

  have : ‖Complex.Gamma (v + m)‖ = ‖∏ k ∈ Finset.range m, (v + k)‖ * ‖Complex.Gamma v‖ := by
    have hGm : Complex.Gamma (v + m) ≠ 0 := by
      intro h0
      rw [h0, inv_zero, mul_zero, inv_eq_zero] at h
      exact hv0 h
    have hGm' : 0 < ‖Complex.Gamma (v + m)‖ := norm_pos_iff.mpr hGm
    field_simp at hnorm ⊢
    linarith [hnorm]
  rw [this]
  exact le_mul_of_one_le_left hpos.le hprod

private theorem exists_bound_realGamma (R : ℝ) : ∃ G : ℝ, ∀ x : ℝ, 1 ≤ x → x ≤ R → Real.Gamma x ≤ G := by
  have hc : ContinuousOn Real.Gamma (Set.Icc 1 R) := fun x hx => by
    have hx1 := hx.1
    refine (Real.differentiableAt_Gamma fun m h => ?_).continuousAt.continuousWithinAt
    rw [h] at hx1
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  obtain ⟨G, hG⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨G, fun x h1 hR => ?_⟩
  calc Real.Gamma x ≤ |Real.Gamma x| := le_abs_self _
    _ = ‖Real.Gamma x‖ := (Real.norm_eq_abs _).symm
    _ ≤ G := hG x ⟨h1, hR⟩

private theorem exists_bound_invGamma_rect (A B : ℝ) :
    ∃ K : ℝ, ∀ w : ℂ, A ≤ w.re → w.re ≤ B → |w.im| ≤ 1 → ‖(Complex.Gamma w)⁻¹‖ ≤ K := by
  set S : Set ℂ := {w | A ≤ w.re ∧ w.re ≤ B ∧ |w.im| ≤ 1} with hS
  have hclosed : IsClosed S := by
    have h1 : IsClosed {w : ℂ | A ≤ w.re} := isClosed_le continuous_const Complex.continuous_re
    have h2 : IsClosed {w : ℂ | w.re ≤ B} := isClosed_le Complex.continuous_re continuous_const
    have h3 : IsClosed {w : ℂ | |w.im| ≤ 1} :=
      isClosed_le (continuous_abs.comp Complex.continuous_im) continuous_const
    exact (h1.inter (h2.inter h3))
  have hbdd : Bornology.IsBounded S := by
    refine (Metric.isBounded_iff_subset_closedBall 0).mpr ⟨|A| + |B| + 1, fun w hw => ?_⟩
    obtain ⟨h1, h2, h3⟩ := hw
    rw [Metric.mem_closedBall, dist_zero_right]
    calc ‖w‖ ≤ |w.re| + |w.im| := Complex.norm_le_abs_re_add_abs_im w
      _ ≤ (|A| + |B|) + 1 := by
          gcongr
          exact abs_le.mpr ⟨by linarith [neg_abs_le A, abs_nonneg B], by linarith [le_abs_self B, abs_nonneg A]⟩
  have hcomp : IsCompact S := Metric.isCompact_of_isClosed_isBounded hclosed hbdd
  have hcont : ContinuousOn (fun w : ℂ => (Complex.Gamma w)⁻¹) S :=
    Complex.differentiable_one_div_Gamma.continuous.continuousOn
  obtain ⟨K, hK⟩ := hcomp.exists_bound_of_continuousOn hcont
  exact ⟨K, fun w h1 h2 h3 => hK w ⟨h1, h2, h3⟩⟩

private theorem exists_bound_invGamma_of_one_le (R : ℝ) :
    ∃ K : ℝ, ∀ w : ℂ, 1 ≤ w.re → w.re ≤ R → ‖(Complex.Gamma w)⁻¹‖ ≤ K * Real.exp (Real.pi * |w.im|) := by
  obtain ⟨m, hm⟩ := exists_nat_ge R
  obtain ⟨G, hG⟩ := exists_bound_realGamma (m + 1)
  obtain ⟨K₀, hK₀⟩ := exists_bound_invGamma_rect 1 R
  refine ⟨max K₀ 0 + max G 0 / Real.pi, fun w h1 hR => ?_⟩
  have hexp1 : 1 ≤ Real.exp (Real.pi * |w.im|) := Real.one_le_exp (by positivity)
  have hGpi : 0 ≤ max G 0 / Real.pi := div_nonneg (le_max_right _ _) Real.pi_pos.le
  rcases le_or_gt |w.im| 1 with him | him
  · calc ‖(Complex.Gamma w)⁻¹‖ ≤ K₀ := hK₀ w h1 hR him
      _ ≤ max K₀ 0 := le_max_left _ _
      _ ≤ (max K₀ 0 + max G 0 / Real.pi) * 1 := by rw [mul_one]; linarith
      _ ≤ (max K₀ 0 + max G 0 / Real.pi) * Real.exp (Real.pi * |w.im|) := by
          gcongr
  ·
    have him : w.im ≠ 0 := fun h0 => by rw [h0, abs_zero] at him; linarith
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hsin : Complex.sin (Real.pi * w) ≠ 0 := by
      intro h0
      obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp h0
      have h1 := congrArg Complex.im hk
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.intCast_re, Complex.intCast_im,
        zero_mul, mul_zero, add_zero] at h1
      exact him ((mul_eq_zero.mp h1).resolve_left Real.pi_ne_zero)
    have hrefl : (Complex.Gamma w)⁻¹ = Complex.Gamma (1 - w) * Complex.sin (Real.pi * w) / Real.pi := by
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← mul_div_assoc, ← mul_assoc, Complex.Gamma_mul_Gamma_one_sub]
      field_simp
    have hv : 1 ≤ |(1 - w).im| := by simp; linarith
    have hG1 : ‖Complex.Gamma (1 - w)‖ ≤ max G 0 := by
      calc ‖Complex.Gamma (1 - w)‖ ≤ ‖Complex.Gamma (1 - w + ((m + 1 : ℕ) : ℂ))‖ :=
            norm_Gamma_le_norm_Gamma_add hv (m + 1)
        _ ≤ Real.Gamma (1 - w + ((m + 1 : ℕ) : ℂ)).re := by
            apply norm_Gamma_le_Gamma_re
            simp
            linarith
        _ ≤ G := by
            apply hG
            · simp; linarith
            · simp; linarith
        _ ≤ max G 0 := le_max_left _ _
    have hsinle : ‖Complex.sin (Real.pi * w)‖ ≤ Real.exp (Real.pi * |w.im|) := by
      calc ‖Complex.sin (Real.pi * w)‖ ≤ Real.exp |((Real.pi : ℂ) * w).im| := norm_sin_le_exp_abs_im _
        _ = Real.exp (Real.pi * |w.im|) := by
            congr 1
            simp [abs_mul, abs_of_pos Real.pi_pos]
    rw [hrefl, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    calc ‖Complex.Gamma (1 - w)‖ * ‖Complex.sin (Real.pi * w)‖ / Real.pi
        ≤ max G 0 * Real.exp (Real.pi * |w.im|) / Real.pi := by gcongr
      _ = max G 0 / Real.pi * Real.exp (Real.pi * |w.im|) := by ring
      _ ≤ (max K₀ 0 + max G 0 / Real.pi) * Real.exp (Real.pi * |w.im|) := by
          gcongr
          linarith [le_max_right K₀ 0]

private theorem exists_bound_invGamma_strip (A B : ℝ) :
    ∃ C D : ℝ, ∀ z : ℂ, A ≤ z.re → z.re ≤ B → ‖(Complex.Gamma z)⁻¹‖ ≤ C * Real.exp (D * |z.im|) := by
  set n : ℕ := ⌈1 - A⌉₊ with hn
  have hnA : 1 - A ≤ n := Nat.le_ceil _
  obtain ⟨K, hK⟩ := exists_bound_invGamma_of_one_le (B + n)
  set R₀ : ℝ := |A| + |B| with hR₀
  refine ⟨(n.factorial : ℝ) * Real.exp (R₀ + n) * max K 0, 1 + Real.pi, fun z hA hB => ?_⟩

  have hw1 : 1 ≤ (z + n).re := by simp; linarith
  have hw2 : (z + n).re ≤ B + n := by simp; linarith
  have hwim : (z + n).im = z.im := by simp
  have hKz : ‖(Complex.Gamma (z + n))⁻¹‖ ≤ max K 0 * Real.exp (Real.pi * |z.im|) := by
    calc ‖(Complex.Gamma (z + n))⁻¹‖ ≤ K * Real.exp (Real.pi * |(z + n).im|) := hK _ hw1 hw2
      _ ≤ max K 0 * Real.exp (Real.pi * |z.im|) := by rw [hwim]; gcongr; exact le_max_left _ _

  have hz : ‖z‖ ≤ R₀ + |z.im| := by
    calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
      _ ≤ R₀ + |z.im| := by
          gcongr
          exact abs_le.mpr ⟨by linarith [neg_abs_le A, abs_nonneg B], by linarith [le_abs_self B, abs_nonneg A]⟩
  have hR₀0 : 0 ≤ R₀ := by positivity
  have hprod : ‖∏ k ∈ Finset.range n, (z + k)‖ ≤ (n.factorial : ℝ) * Real.exp (R₀ + n) * Real.exp |z.im| := by
    rw [norm_prod]
    have h1 : ∏ k ∈ Finset.range n, ‖z + (k : ℂ)‖ ≤ ∏ _k ∈ Finset.range n, (R₀ + n + |z.im|) := by
      refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun k hk => ?_
      have hk' : (k : ℝ) ≤ n := by exact_mod_cast (Finset.mem_range.mp hk).le
      calc ‖z + (k : ℂ)‖ ≤ ‖z‖ + ‖(k : ℂ)‖ := norm_add_le _ _
        _ = ‖z‖ + k := by simp
        _ ≤ (R₀ + |z.im|) + n := by gcongr
        _ = R₀ + n + |z.im| := by ring
    rw [Finset.prod_const, Finset.card_range] at h1
    have h2 : (R₀ + n + |z.im|) ^ n ≤ (n.factorial : ℝ) * Real.exp (R₀ + n + |z.im|) := by
      have h := Real.pow_div_factorial_le_exp (x := R₀ + n + |z.im|) (by positivity) n
      have hf : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
      rwa [div_le_iff₀ hf, mul_comm] at h
    calc ∏ k ∈ Finset.range n, ‖z + (k : ℂ)‖ ≤ (R₀ + n + |z.im|) ^ n := h1
      _ ≤ (n.factorial : ℝ) * Real.exp (R₀ + n + |z.im|) := h2
      _ = (n.factorial : ℝ) * Real.exp (R₀ + n) * Real.exp |z.im| := by rw [Real.exp_add]; ring
  rw [inv_Gamma_eq_prod_mul z n, norm_mul]
  calc ‖∏ k ∈ Finset.range n, (z + k)‖ * ‖(Complex.Gamma (z + n))⁻¹‖
      ≤ ((n.factorial : ℝ) * Real.exp (R₀ + n) * Real.exp |z.im|) * (max K 0 * Real.exp (Real.pi * |z.im|)) :=
        mul_le_mul hprod hKz (norm_nonneg _) (by positivity)
    _ = (n.factorial : ℝ) * Real.exp (R₀ + n) * max K 0 * Real.exp ((1 + Real.pi) * |z.im|) := by
        rw [show (1 + Real.pi) * |z.im| = |z.im| + Real.pi * |z.im| by ring]
        simp only [Real.exp_add]
        ring

private theorem exists_bound_invGammaℝ_strip (A B : ℝ) :
    ∃ C D : ℝ, ∀ w : ℂ, A ≤ w.re → w.re ≤ B → ‖(Complex.Gammaℝ w)⁻¹‖ ≤ C * Real.exp (D * |w.im|) := by
  obtain ⟨C, D, hCD⟩ := exists_bound_invGamma_strip (A / 2) (B / 2)
  have hpi1 : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  refine ⟨Real.pi ^ (max (B / 2) 0) * C, D / 2, fun w hA hB => ?_⟩
  have hre : (w / 2).re = w.re / 2 := by simp
  have him : (w / 2).im = w.im / 2 := by simp
  have hG := hCD (w / 2) (by rw [hre]; linarith) (by rw [hre]; linarith)
  have hre' : (-w / 2).re = -(w.re / 2) := by simp [neg_div]
  rw [Complex.Gammaℝ_def, mul_inv, norm_mul, norm_inv, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos, hre',
    Real.rpow_neg Real.pi_pos.le, inv_inv]
  have hpow : Real.pi ^ (w.re / 2) ≤ Real.pi ^ (max (B / 2) 0) :=
    Real.rpow_le_rpow_of_exponent_le hpi1 (le_max_of_le_left (by linarith))
  have hC0 : 0 ≤ C * Real.exp (D * |(w / 2).im|) := le_trans (norm_nonneg _) hG
  calc Real.pi ^ (w.re / 2) * ‖(Complex.Gamma (w / 2))⁻¹‖
      ≤ Real.pi ^ (max (B / 2) 0) * (C * Real.exp (D * |(w / 2).im|)) :=
        mul_le_mul hpow hG (norm_nonneg _) (by positivity)
    _ = Real.pi ^ (max (B / 2) 0) * C * Real.exp (D / 2 * |w.im|) := by
        rw [him, abs_div, abs_two]
        ring_nf

end W3

namespace W3

private theorem hasDerivAt_ofReal' (x : ℝ) : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := by
  first | simpa using Complex.ofRealCLM.hasDerivAt (x := x) | (have h' := Complex.ofRealCLM.hasDerivAt (x := x); simp at h'; exact h') | exact Complex.ofRealCLM.hasDerivAt (x := x)

end W3

namespace W3

end W3

namespace W3

end W3

namespace W3

private theorem rpow_le_rpow_add_rpow {r e e₁ e₂ : ℝ} (hr : 0 < r) (h₁ : e₁ ≤ e) (h₂ : e ≤ e₂) :
    r ^ e ≤ r ^ e₁ + r ^ e₂ := by
  rcases le_or_gt r 1 with hr1 | hr1
  · exact (Real.rpow_le_rpow_of_exponent_ge hr hr1 h₁).trans (le_add_of_nonneg_right (by positivity))
  · exact (Real.rpow_le_rpow_of_exponent_le hr1.le h₂).trans (le_add_of_nonneg_left (by positivity))

private theorem abs_log_le_rpow_add_rpow_div {r η : ℝ} (hr : 0 < r) (hη : 0 < η) :
    |Real.log r| ≤ (r ^ η + r ^ (-η)) / η := by
  have h1 : Real.log r ≤ r ^ η / η := Real.log_le_rpow_div hr.le hη
  have h2 : Real.log r⁻¹ ≤ r⁻¹ ^ η / η := Real.log_le_rpow_div (inv_nonneg.mpr hr.le) hη
  rw [Real.log_inv, Real.inv_rpow hr.le, ← Real.rpow_neg hr.le] at h2
  have hp1 : 0 ≤ r ^ η / η := by positivity
  have hp2 : 0 ≤ r ^ (-η) / η := by positivity
  rw [abs_le, add_div]
  constructor <;> linarith

end W3

namespace W3

open scoped Topology

private theorem entire_eq_of_eqOn_open {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g) {U : Set ℂ}
    (hU : IsOpen U) {z₀ : ℂ} (hz₀ : z₀ ∈ U) (h : ∀ z ∈ U, f z = g z) : f = g :=
  AnalyticOnNhd.eq_of_eventuallyEq (fun z _ => hf.analyticAt z) (fun z _ => hg.analyticAt z)
    (z₀ := z₀) (Filter.eventually_of_mem (hU.mem_nhds hz₀) h)

private theorem isOpen_re_pos : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re

private theorem isOpen_re_lt_one : IsOpen {z : ℂ | z.re < 1} := isOpen_lt Complex.continuous_re continuous_const

private theorem ext_of_eqOn_rect {f g : ℂ → ℂ → ℂ}
    (hf₁ : ∀ w₂, Differentiable ℂ fun w₁ => f w₁ w₂) (hg₁ : ∀ w₂, Differentiable ℂ fun w₁ => g w₁ w₂)
    (hf₂ : ∀ w₁, Differentiable ℂ fun w₂ => f w₁ w₂) (hg₂ : ∀ w₁, Differentiable ℂ fun w₂ => g w₁ w₂)
    {U₁ U₂ : Set ℂ} (hU₁ : IsOpen U₁) (hU₂ : IsOpen U₂) {z₁ z₂ : ℂ} (hz₁ : z₁ ∈ U₁) (hz₂ : z₂ ∈ U₂)
    (h : ∀ w₁ ∈ U₁, ∀ w₂ ∈ U₂, f w₁ w₂ = g w₁ w₂) : ∀ w₁ w₂, f w₁ w₂ = g w₁ w₂ := by
  have step1 : ∀ w₂ ∈ U₂, ∀ w₁, f w₁ w₂ = g w₁ w₂ := by
    intro w₂ hw₂ w₁
    have e := entire_eq_of_eqOn_open (hf₁ w₂) (hg₁ w₂) hU₁ hz₁ (fun z hz => h z hz w₂ hw₂)
    exact congrFun e w₁
  intro w₁ w₂
  have e := entire_eq_of_eqOn_open (hf₂ w₁) (hg₂ w₁) hU₂ hz₂ (fun z hz => step1 z hz w₁)
  exact congrFun e w₂

end W3

namespace W3

private theorem exists_bound_invGammaℝ_strip' (A B : ℝ) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ w : ℂ, A ≤ w.re → w.re ≤ B → ‖(Gammaℝ w)⁻¹‖ ≤ C * Real.exp (D * |w.im|) := by
  obtain ⟨C, D, hCD⟩ := exists_bound_invGammaℝ_strip A B
  refine ⟨|C|, |D|, abs_nonneg C, abs_nonneg D, fun w h1 h2 => ?_⟩
  have h := hCD w h1 h2
  have hE : Real.exp (D * |w.im|) ≤ Real.exp (|D| * |w.im|) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_abs_self D) (abs_nonneg _))
  calc ‖(Gammaℝ w)⁻¹‖ ≤ C * Real.exp (D * |w.im|) := h
    _ ≤ |C| * Real.exp (D * |w.im|) := mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le
    _ ≤ |C| * Real.exp (|D| * |w.im|) := mul_le_mul_of_nonneg_left hE (abs_nonneg C)

end W3

end TateReal

namespace TateReal

namespace W2

open W3 LanglandsTunnell.Converse.ArchR

section Auxiliary

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

end Auxiliary

section Kernel

end Kernel

section Bridge

variable (u₁ u₂ u : ℂ) (a₁ a₂ a : ZMod 2) (s : ℂ) (g : Matrix (Fin 2) (Fin 2) ℝ)

end Bridge

end W2

end TateReal

end

end

section

open Complex MeasureTheory LanglandsTunnell.TateLocal LanglandsTunnell.ArchPlace

noncomputable section

namespace TateComplex

private def kerC (k : ℤ) (w : ℂ) (z : ℂ) : ℂ :=
  (z / ((‖z‖ : ℝ) : ℂ)) ^ k * (((‖z‖ ^ 2 : ℝ)) : ℂ) ^ (w - 1)

private def tateZetaC (f : ℂ → ℂ) (k : ℤ) (w : ℂ) : ℂ := ∫ z : ℂ, f z * kerC k w z

private theorem tateZetaC_eq_integral_ker (f : ℂ → ℂ) (k : ℤ) (w : ℂ) :
    tateZetaC f k w = ∫ z : ℂ, f z * kerC k w z := rfl

private def _root_.TateComplex.FC (f : ℂ → ℂ) : ℂ → ℂ := tateFourier psiComplex volume f

p2m_export "TateComplex" "FC"
private def gaussPolyC (p : MvPolynomial (Fin 2) ℂ) (α : ℝ) (β₁ β₂ : ℂ) (z : ℂ) : ℂ :=
  MvPolynomial.eval ![z, starRingEnd ℂ z] p
    * cexp (-(2 * Real.pi * α * ‖z‖ ^ 2) + 2 * Real.pi * (β₁ * z + β₂ * starRingEnd ℂ z))

private def IsGaussPolyC (f : ℂ → ℂ) : Prop :=
  ∃ (p : MvPolynomial (Fin 2) ℂ) (α : ℝ) (β₁ β₂ : ℂ), 0 < α ∧ f = gaussPolyC p α β₁ β₂

private def cC (k : ℤ) : ℂ := (-I) ^ k.natAbs / 2

section
open Complex MeasureTheory LanglandsTunnell.TateLocal LanglandsTunnell.ArchPlace

private theorem isGaussPolyC_complexTestFun' (k : ℤ) : IsGaussPolyC (complexTestFun k) := by
  refine ⟨MvPolynomial.X 1 ^ k.toNat * MvPolynomial.X 0 ^ (-k).toNat, 1, 0, 0, one_pos, ?_⟩
  funext z
  simp only [complexTestFun, gaussPolyC, MvPolynomial.eval_mul, MvPolynomial.eval_pow, MvPolynomial.eval_X,
    Matrix.cons_val_one, Matrix.cons_val_zero, Complex.ofReal_one, mul_one, zero_mul, add_zero, mul_zero]

private def ProdForm (f : ℂ → ℂ) : Prop :=
  ∃ (α' : ℝ) (β γ : ℂ) (s : Finset (Fin 2 →₀ ℕ)) (p q : (Fin 2 →₀ ℕ) → Polynomial ℂ), 0 < α' ∧
    ∀ x t : ℝ, f (x + t * I) = ∑ m ∈ s, TateReal.gaussPoly (p m) α' β x * TateReal.gaussPoly (q m) α' γ t

private def toXT (p : MvPolynomial (Fin 2) ℂ) : MvPolynomial (Fin 2) ℂ :=
  MvPolynomial.bind₁ ![MvPolynomial.X 0 + MvPolynomial.C I * MvPolynomial.X 1,
    MvPolynomial.X 0 - MvPolynomial.C I * MvPolynomial.X 1] p

private theorem eval_toXT (p : MvPolynomial (Fin 2) ℂ) (x t : ℝ) :
    MvPolynomial.eval ![(x : ℂ), t] (toXT p) = MvPolynomial.eval ![(x + t * I : ℂ), starRingEnd ℂ (x + t * I)] p := by
  unfold toXT
  rw [MvPolynomial.eval, MvPolynomial.eval₂Hom_bind₁]
  refine congrArg (fun w : Fin 2 → ℂ => MvPolynomial.eval₂Hom (RingHom.id ℂ) w p) ?_
  funext i
  fin_cases i <;> simp [Complex.conj_ofReal] <;> ring

private theorem cexp_split (α : ℝ) (β₁ β₂ : ℂ) (x t : ℝ) :
    cexp (-(2 * Real.pi * α * ‖(x + t * I : ℂ)‖ ^ 2)
        + 2 * Real.pi * (β₁ * (x + t * I) + β₂ * starRingEnd ℂ (x + t * I)))
      = cexp (-Real.pi * (2 * α) * (x : ℂ) ^ 2 + 2 * Real.pi * (β₁ + β₂) * x)
        * cexp (-Real.pi * (2 * α) * (t : ℂ) ^ 2 + 2 * Real.pi * (I * (β₁ - β₂)) * t) := by
  rw [← Complex.exp_add]
  congr 1
  have hn : (‖(x + t * I : ℂ)‖ ^ 2 : ℂ) = (x : ℂ) ^ 2 + (t : ℂ) ^ 2 := by
    have := Complex.sq_norm (x + t * I)
    rw [Complex.normSq_apply] at this
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero, Complex.ofReal_im,
      Complex.I_im, mul_one, sub_self, add_zero, Complex.add_im, Complex.mul_im, zero_add] at this
    have h2 : ‖(x + t * I : ℂ)‖ ^ 2 = x ^ 2 + t ^ 2 := by rw [this]; ring
    exact_mod_cast h2
  rw [hn]
  simp only [map_add, Complex.conj_ofReal, map_mul, Complex.conj_I]
  ring

private theorem IsGaussPolyC.prodForm {f : ℂ → ℂ} (hf : IsGaussPolyC f) : ProdForm f := by
  obtain ⟨p, α, β₁, β₂, hα, rfl⟩ := hf
  refine ⟨2 * α, β₁ + β₂, I * (β₁ - β₂), (toXT p).support,
    fun m => Polynomial.C (MvPolynomial.coeff m (toXT p)) * Polynomial.X ^ m 0, fun m => Polynomial.X ^ m 1,
    by positivity, fun x t => ?_⟩
  simp only [gaussPolyC]
  rw [← eval_toXT, cexp_split, MvPolynomial.eval_eq', Finset.sum_mul]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [TateReal.gaussPoly, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
    Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  push_cast
  ring

private def fromXT (r : MvPolynomial (Fin 2) ℂ) : MvPolynomial (Fin 2) ℂ :=
  MvPolynomial.bind₁ ![(MvPolynomial.X 0 + MvPolynomial.X 1) * MvPolynomial.C (1 / 2 : ℂ),
    (MvPolynomial.X 0 - MvPolynomial.X 1) * MvPolynomial.C (-I / 2)] r

private theorem eval_fromXT (r : MvPolynomial (Fin 2) ℂ) (z : ℂ) :
    MvPolynomial.eval ![z, starRingEnd ℂ z] (fromXT r) = MvPolynomial.eval ![(z.re : ℂ), z.im] r := by
  unfold fromXT
  rw [MvPolynomial.eval, MvPolynomial.eval₂Hom_bind₁]
  refine congrArg (fun w : Fin 2 → ℂ => MvPolynomial.eval₂Hom (RingHom.id ℂ) w r) ?_
  funext i
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    simp [Complex.add_conj]
    ring
  · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one]
    simp [Complex.sub_conj]
    ring_nf
    simp only [Complex.I_sq]
    ring

private theorem eval_aeval_X (P : Polynomial ℂ) (i : Fin 2) (v : Fin 2 → ℂ) :
    MvPolynomial.eval v (Polynomial.aeval (MvPolynomial.X i : MvPolynomial (Fin 2) ℂ) P) = P.eval (v i) := by
  have h := Polynomial.aeval_algHom_apply (MvPolynomial.aeval v) (MvPolynomial.X i : MvPolynomial (Fin 2) ℂ) P
  rw [MvPolynomial.aeval_X, Polynomial.coe_aeval_eq_eval] at h
  simpa using h.symm

private theorem ProdForm.isGaussPolyC {f : ℂ → ℂ} (hf : ProdForm f) : IsGaussPolyC f := by
  obtain ⟨α', β, γ, s, p, q, hα', hf⟩ := hf
  set r : MvPolynomial (Fin 2) ℂ := ∑ m ∈ s,
    Polynomial.aeval (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℂ) (p m)
      * Polynomial.aeval (MvPolynomial.X 1 : MvPolynomial (Fin 2) ℂ) (q m) with hr
  refine ⟨fromXT r, α' / 2, (β - I * γ) / 2, (β + I * γ) / 2, by positivity, ?_⟩
  funext z
  have key : ∀ x t : ℝ,
      f (x + t * I) = gaussPolyC (fromXT r) (α' / 2) ((β - I * γ) / 2) ((β + I * γ) / 2) (x + t * I) := by
    intro x t
    rw [hf x t]
    simp only [gaussPolyC]
    rw [eval_fromXT, cexp_split]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero, Complex.ofReal_im,
      Complex.I_im, mul_one, sub_self, add_zero, Complex.add_im, Complex.mul_im, zero_add]
    rw [hr, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [map_mul, eval_aeval_X, eval_aeval_X]
    simp only [TateReal.gaussPoly, Matrix.cons_val_zero, Matrix.cons_val_one]
    have e₁ : (-Real.pi * (2 * ((α' / 2 : ℝ) : ℂ)) * (x : ℂ) ^ 2
          + 2 * Real.pi * ((β - I * γ) / 2 + (β + I * γ) / 2) * x)
        = -Real.pi * α' * (x : ℂ) ^ 2 + 2 * Real.pi * β * x := by
      push_cast; ring
    have e₂ : (-Real.pi * (2 * ((α' / 2 : ℝ) : ℂ)) * (t : ℂ) ^ 2
          + 2 * Real.pi * (I * ((β - I * γ) / 2 - (β + I * γ) / 2)) * t)
        = -Real.pi * α' * (t : ℂ) ^ 2 + 2 * Real.pi * γ * t := by
      push_cast; ring_nf; simp only [Complex.I_sq]; ring
    rw [e₁, e₂]
    ring
  have hz := key z.re z.im
  rwa [Complex.re_add_im] at hz

private theorem psiComplex_coords (x t a b : ℝ) :
    psiComplex ((x + t * I) * (a + b * I))
      = cexp (((-2 * Real.pi * x * (2 * a) : ℝ) : ℂ) * I) * cexp (((-2 * Real.pi * t * (-2 * b) : ℝ) : ℂ) * I) := by
  rw [psiComplex_apply, ← Complex.exp_add]
  congr 1
  simp only [map_mul, map_add, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  linear_combination (-4 * (Real.pi : ℂ) * (t : ℂ) * (b : ℂ) * I) * Complex.I_sq

private theorem gaussPoly_mul_left (P : Polynomial ℂ) (A : ℝ) (B : ℂ) (c x : ℝ) :
    TateReal.gaussPoly P A B (c * x)
      = TateReal.gaussPoly (P.comp (Polynomial.C (c : ℂ) * Polynomial.X)) (c ^ 2 * A) (c * B) x := by
  simp only [TateReal.gaussPoly, Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  push_cast
  ring_nf

end

private theorem isGaussPolyC_complexTestFun (k : ℤ) : IsGaussPolyC (complexTestFun k) :=
  isGaussPolyC_complexTestFun' k

section
open Complex MeasureTheory LanglandsTunnell.TateLocal LanglandsTunnell.ArchPlace
open scoped FourierTransform

private theorem integral_complex_eq_prod (F : ℂ → ℂ) : ∫ z : ℂ, F z = ∫ pt : ℝ × ℝ, F (pt.1 + pt.2 * I) := by
  rw [← (Complex.volume_preserving_equiv_real_prod.symm _).integral_comp
    Complex.measurableEquivRealProd.symm.measurableEmbedding F]
  congr 1
  funext pt
  exact congrArg F (Complex.equivRealProd_symm_apply pt)

private theorem integrable_kernel_mul_gaussPoly (P : Polynomial ℂ) {A : ℝ} (hA : 0 < A) (B : ℂ) (w : ℝ) :
    Integrable fun x : ℝ => cexp (((-2 * Real.pi * x * w : ℝ) : ℂ) * I) * TateReal.gaussPoly P A B x := by
  refine (TateReal.isGaussPoly_gaussPoly P hA B).integrable.bdd_mul (c := 1) ?_
    (Filter.Eventually.of_forall fun x => ?_)
  · exact (Continuous.aestronglyMeasurable (by fun_prop))
  · exact (Complex.norm_exp_ofReal_mul_I _).le

private theorem integral_kernel_mul_eq_fourier (g : ℝ → ℂ) (w : ℝ) :
    ∫ x : ℝ, cexp (((-2 * Real.pi * x * w : ℝ) : ℂ) * I) * g x = 𝓕 g w := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]

private theorem ProdForm.FC {f : ℂ → ℂ} (hf : ProdForm f) : ProdForm (TateComplex.FC f) := by
  obtain ⟨α', β, γ, s, p, q, hα', hf⟩ := hf
  choose P hP using fun m => TateReal.fourier_gaussPoly (p m) hα' β
  choose Q hQ using fun m => TateReal.fourier_gaussPoly (q m) hα' γ
  have hα'' : 0 < 1 / α' := by positivity
  refine ⟨(2 : ℝ) ^ 2 * (1 / α'), ((2 : ℝ) : ℂ) * (-I * β / α'), ((-2 : ℝ) : ℂ) * (-I * γ / α'), s,
    fun m => (P m).comp (Polynomial.C ((2 : ℝ) : ℂ) * Polynomial.X),
    fun m => (Q m).comp (Polynomial.C ((-2 : ℝ) : ℂ) * Polynomial.X), by positivity, fun a b => ?_⟩

  show tateFourier psiComplex volume f (a + b * I) = _
  unfold tateFourier
  rw [integral_complex_eq_prod]
  have hint : ∀ pt : ℝ × ℝ, f (pt.1 + pt.2 * I) * psiComplex ((pt.1 + pt.2 * I) * (a + b * I))
      = ∑ m ∈ s,
          (cexp (((-2 * Real.pi * pt.1 * (2 * a) : ℝ) : ℂ) * I) * TateReal.gaussPoly (p m) α' β pt.1)
            * (cexp (((-2 * Real.pi * pt.2 * (-2 * b) : ℝ) : ℂ) * I) * TateReal.gaussPoly (q m) α' γ pt.2) := by
    intro pt
    rw [hf, psiComplex_coords, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    ring
  simp_rw [hint]
  rw [integral_finsetSum s fun m _ => ?_]
  · refine Finset.sum_congr rfl fun m _ => ?_
    have key := integral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
      (fun x : ℝ => cexp (((-2 * Real.pi * x * (2 * a) : ℝ) : ℂ) * I) * TateReal.gaussPoly (p m) α' β x)
      (fun t : ℝ => cexp (((-2 * Real.pi * t * (-2 * b) : ℝ) : ℂ) * I) * TateReal.gaussPoly (q m) α' γ t)
    try simp only at key
    rw [Measure.volume_eq_prod, key, integral_kernel_mul_eq_fourier, integral_kernel_mul_eq_fourier,
      hP m, hQ m, gaussPoly_mul_left, gaussPoly_mul_left]
    rw [show ((-2 : ℝ)) ^ 2 * (1 / α') = (2 : ℝ) ^ 2 * (1 / α') by norm_num]
  · rw [Measure.volume_eq_prod]
    exact (integrable_kernel_mul_gaussPoly (p m) hα' β (2 * a)).mul_prod
      (integrable_kernel_mul_gaussPoly (q m) hα' γ (-2 * b))

private theorem IsGaussPolyC.FC' {f : ℂ → ℂ} (hf : IsGaussPolyC f) : IsGaussPolyC (TateComplex.FC f) :=
  hf.prodForm.FC.isGaussPolyC

end

private theorem IsGaussPolyC.FC {f : ℂ → ℂ} (hf : IsGaussPolyC f) : IsGaussPolyC (TateComplex.FC f) :=
  IsGaussPolyC.FC' hf

section
open Complex MeasureTheory Set LanglandsTunnell.TateLocal LanglandsTunnell.ArchPlace
open scoped ENNReal

private theorem integrable_of_radial_bound {F : ℂ → ℂ} {G : ℝ → ℝ} (hF : AEStronglyMeasurable F volume)
    (hG : IntegrableOn (fun r : ℝ => r * G r) (Ioi 0)) (hG0 : ∀ r ∈ Ioi (0 : ℝ), 0 ≤ G r)
    (hbound : ∀ z : ℂ, z ≠ 0 → ‖F z‖ ≤ G ‖z‖) : Integrable F := by
  refine ⟨hF, ?_⟩
  rw [hasFiniteIntegral_iff_norm]

  have hle : ∫⁻ z : ℂ, ENNReal.ofReal ‖F z‖ ≤ ∫⁻ z : ℂ, ENNReal.ofReal (G ‖z‖) := by
    have h0 : ∀ᵐ z : ℂ ∂volume, z ≠ 0 := by
      rw [ae_iff]; simp
    refine lintegral_mono_ae (h0.mono fun z hz => ?_)
    exact ENNReal.ofReal_le_ofReal (hbound z hz)
  refine lt_of_le_of_lt hle ?_
  rw [← Complex.lintegral_comp_polarCoord_symm, polarCoord_target]
  have hpt : ∀ p ∈ Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
      ENNReal.ofReal p.1 • ENNReal.ofReal (G ‖(Complex.polarCoord.symm p : ℂ)‖)
        = ENNReal.ofReal (p.1 * G p.1) * (1 : ℝ≥0∞) := by
    rintro ⟨r, θ⟩ ⟨hr, -⟩
    have hr : 0 < r := hr
    simp only [smul_eq_mul, mul_one]
    rw [show (Complex.polarCoord.symm (r, θ) : ℂ) = (r : ℂ) * cexp ((θ : ℂ) * I) by
          rw [Complex.polarCoord_symm_apply, Complex.exp_mul_I]; push_cast; ring,
      norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
      ENNReal.ofReal_mul hr.le]
  have key := lintegral_prod_mul (μ := volume.restrict (Ioi (0 : ℝ))) (ν := volume.restrict (Ioo (-Real.pi) Real.pi))
    (f := fun r : ℝ => ENNReal.ofReal (r * G r)) (g := fun _ : ℝ => (1 : ℝ≥0∞)) hG.aemeasurable.ennreal_ofReal
    aemeasurable_const
  try simp only at key
  rw [setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) hpt, Measure.volume_eq_prod,
    ← Measure.prod_restrict, key]
  refine ENNReal.mul_lt_top ?_ ?_
  · have := hG.2
    rw [hasFiniteIntegral_iff_norm] at this
    refine lt_of_le_of_lt (lintegral_mono_ae ?_) this
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (le_of_lt hr) (hG0 r hr))]
  · simp [Real.volume_Ioo]

private theorem norm_kerC {z : ℂ} (hz : z ≠ 0) (k : ℤ) (w : ℂ) : ‖kerC k w z‖ = (‖z‖ ^ 2) ^ (w.re - 1) := by
  have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
  unfold kerC
  rw [norm_mul, Complex.norm_zpow, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm, div_self hn.ne',
    one_zpow, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), Complex.sub_re, Complex.one_re]

private theorem norm_gaussPolyC_le (p : MvPolynomial (Fin 2) ℂ) (α : ℝ) (β₁ β₂ : ℂ) (z : ℂ) :
    ‖gaussPolyC p α β₁ β₂ z‖
      ≤ (∑ m ∈ p.support, ‖MvPolynomial.coeff m p‖ * ‖z‖ ^ (m 0 + m 1))
          * Real.exp (-(2 * Real.pi * α) * ‖z‖ ^ 2 + 2 * Real.pi * (‖β₁‖ + ‖β₂‖) * ‖z‖) := by
  unfold gaussPolyC
  rw [norm_mul]
  refine mul_le_mul ?_ ?_ (norm_nonneg _) (Finset.sum_nonneg fun m _ => by positivity)
  · rw [MvPolynomial.eval_eq']
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)
    rw [norm_mul, Fin.prod_univ_two, norm_mul, norm_pow, norm_pow, pow_add]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Complex.norm_conj, le_refl]
  · rw [Complex.norm_exp]
    refine Real.exp_le_exp.2 ?_
    have h1 : (-(2 * Real.pi * (α : ℂ) * ((‖z‖ : ℝ) : ℂ) ^ 2) + 2 * Real.pi * (β₁ * z + β₂ * starRingEnd ℂ z)).re
        = -(2 * Real.pi * α * ‖z‖ ^ 2) + 2 * Real.pi * (β₁ * z + β₂ * starRingEnd ℂ z).re := by
      simp [Complex.mul_re, Complex.add_re, pow_two]
    rw [h1]
    have h2 : (β₁ * z + β₂ * starRingEnd ℂ z).re ≤ (‖β₁‖ + ‖β₂‖) * ‖z‖ := by
      refine (Complex.re_le_norm _).trans ?_
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul, Complex.norm_conj, add_mul]
    nlinarith [Real.pi_pos, h2]

private theorem integrableOn_radial_term {b : ℝ} (hb : 0 < b) (K : ℝ) (n : ℕ) {a : ℝ} (ha : -1 < a) :
    IntegrableOn (fun r : ℝ => r * (r ^ n * (r ^ 2) ^ a * Real.exp (-b * r ^ 2 + K * r))) (Ioi 0) := by

  set C : ℝ := Real.exp (K ^ 2 / (2 * b)) with hC
  have hint : Integrable (fun r : ℝ => C * (r ^ ((n : ℝ) + 1 + 2 * a) * Real.exp (-(b / 2) * r ^ 2))) :=
    (integrable_rpow_mul_exp_neg_mul_sq (by positivity) (by linarith)).const_mul C
  refine (hint.integrableOn.mono' ?_ ?_)
  · refine (ContinuousOn.mul continuousOn_id ?_).aestronglyMeasurable measurableSet_Ioi
    refine ContinuousOn.mul (ContinuousOn.mul (continuousOn_id.pow n) ?_) (Continuous.continuousOn (by fun_prop))
    exact (continuousOn_id.pow 2).rpow_const fun r hr => Or.inl (pow_ne_zero 2 (ne_of_gt hr))
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hr : 0 < r := hr
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hpow : r * (r ^ n * (r ^ 2) ^ a) = r ^ ((n : ℝ) + 1 + 2 * a) := by
      rw [← Real.rpow_natCast r n, ← Real.rpow_natCast r 2, ← Real.rpow_mul hr.le, ← Real.rpow_add hr,
        show ((n : ℝ) + 1 + 2 * a) = 1 + ((n : ℝ) + ((2 : ℕ) : ℝ) * a) by push_cast; ring,
        Real.rpow_add hr 1 ((n : ℝ) + ((2 : ℕ) : ℝ) * a), Real.rpow_one]
    have hexp : Real.exp (-b * r ^ 2 + K * r) ≤ C * Real.exp (-(b / 2) * r ^ 2) := by
      rw [hC, ← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      have hsq : 0 ≤ (r * Real.sqrt (b / 2) - K / (2 * Real.sqrt (b / 2))) ^ 2 := sq_nonneg _
      have hb2 : 0 < b / 2 := by positivity
      have hs : Real.sqrt (b / 2) ^ 2 = b / 2 := Real.sq_sqrt hb2.le
      have hs0 : 0 < Real.sqrt (b / 2) := Real.sqrt_pos.2 hb2
      rw [sub_sq, mul_pow, hs, div_pow, mul_pow, hs, show K ^ 2 / (2 ^ 2 * (b / 2)) = K ^ 2 / (2 * b) by ring] at hsq
      have hKr : K * r = 2 * (r * Real.sqrt (b / 2)) * (K / (2 * Real.sqrt (b / 2))) := by
        field_simp
      rw [hKr]
      nlinarith [hsq]
    calc r * (r ^ n * (r ^ 2) ^ a * Real.exp (-b * r ^ 2 + K * r))
        = r * (r ^ n * (r ^ 2) ^ a) * Real.exp (-b * r ^ 2 + K * r) := by ring
      _ ≤ r ^ ((n : ℝ) + 1 + 2 * a) * (C * Real.exp (-(b / 2) * r ^ 2)) := by
          rw [hpow]; exact mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = C * (r ^ ((n : ℝ) + 1 + 2 * a) * Real.exp (-(b / 2) * r ^ 2)) := by ring

private theorem continuous_gaussPolyC (p : MvPolynomial (Fin 2) ℂ) (α : ℝ) (β₁ β₂ : ℂ) :
    Continuous (gaussPolyC p α β₁ β₂) := by
  unfold gaussPolyC
  have hv : Continuous fun z : ℂ => (![z, starRingEnd ℂ z] : Fin 2 → ℂ) := by
    refine continuous_pi fun i => ?_
    fin_cases i
    · exact continuous_id
    · exact Complex.continuous_conj
  exact ((MvPolynomial.continuous_eval p).comp hv).mul (by fun_prop)

private theorem measurable_kerC (k : ℤ) (w : ℂ) : Measurable (kerC k w) := by
  refine measurable_of_continuousOn_compl_singleton 0 ?_
  unfold kerC
  refine ContinuousOn.mul ?_ ?_
  · refine ContinuousOn.zpow₀ (ContinuousOn.div continuousOn_id (by fun_prop) fun z hz => ?_) k fun z hz => Or.inl ?_
    · beta_reduce
      exact_mod_cast norm_ne_zero_iff.2 hz
    · have hz' : z ≠ 0 := hz
      exact div_ne_zero hz' (by simpa using norm_ne_zero_iff.2 hz')
  · refine ContinuousOn.cpow_const (Continuous.continuousOn (by fun_prop)) fun z hz => ?_
    have hz' : z ≠ 0 := hz
    exact Complex.ofReal_mem_slitPlane.2 (by positivity)

private theorem integrable_tateC' {f : ℂ → ℂ} (hf : IsGaussPolyC f) (k : ℤ) {w : ℂ} (hw : 0 < w.re) :
    Integrable (fun z : ℂ => f z * kerC k w z) := by
  obtain ⟨p, α, β₁, β₂, hα, rfl⟩ := hf

  refine integrable_of_radial_bound (G := fun r : ℝ => ∑ m ∈ p.support,
      ‖MvPolynomial.coeff m p‖ * (r ^ (m 0 + m 1) * (r ^ 2) ^ (w.re - 1)
        * Real.exp (-(2 * Real.pi * α) * r ^ 2 + 2 * Real.pi * (‖β₁‖ + ‖β₂‖) * r)))
    ((continuous_gaussPolyC p α β₁ β₂).measurable.mul (measurable_kerC k w)).aestronglyMeasurable ?_ ?_ ?_
  · have : (fun r : ℝ => r * ∑ m ∈ p.support, ‖MvPolynomial.coeff m p‖ * (r ^ (m 0 + m 1) * (r ^ 2) ^ (w.re - 1)
        * Real.exp (-(2 * Real.pi * α) * r ^ 2 + 2 * Real.pi * (‖β₁‖ + ‖β₂‖) * r)))
        = fun r : ℝ => ∑ m ∈ p.support, ‖MvPolynomial.coeff m p‖ * (r * (r ^ (m 0 + m 1) * (r ^ 2) ^ (w.re - 1)
        * Real.exp (-(2 * Real.pi * α) * r ^ 2 + 2 * Real.pi * (‖β₁‖ + ‖β₂‖) * r))) := by
      funext r; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun m _ => ?_; ring
    rw [this]
    refine integrable_finsetSum _ fun m _ => ?_
    exact Integrable.const_mul (integrableOn_radial_term (by positivity) (2 * Real.pi * (‖β₁‖ + ‖β₂‖)) (m 0 + m 1)
      (by linarith)) _
  · intro r hr
    have hr : 0 < r := hr
    exact Finset.sum_nonneg fun m _ => by positivity
  · intro z hz
    beta_reduce
    rw [norm_mul, norm_kerC hz]
    refine (mul_le_mul_of_nonneg_right (norm_gaussPolyC_le p α β₁ β₂ z) (by positivity)).trans ?_
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_le_sum fun m _ => le_of_eq ?_
    ring

end

private theorem integrable_tateC {f : ℂ → ℂ} (hf : IsGaussPolyC f) (k : ℤ) {w : ℂ} (hw : 0 < w.re) :
    Integrable (fun z : ℂ => f z * kerC k w z) :=
  integrable_tateC' hf k hw

section
open Complex MeasureTheory Set LanglandsTunnell.TateLocal LanglandsTunnell.ArchPlace

private def rad (k : ℤ) (w : ℂ) (r : ℝ) : ℂ :=
  (r : ℂ) ^ k.natAbs * ((r ^ 2 : ℝ) : ℂ) ^ (w - 1) * cexp (-(2 * (Real.pi : ℂ) * (r : ℂ) ^ 2))

private theorem polarCoord_symm_eq_mul_exp (r θ : ℝ) :
    (Complex.polarCoord.symm (r, θ) : ℂ) = (r : ℂ) * cexp ((θ : ℂ) * I) := by
  rw [Complex.polarCoord_symm_apply, Complex.exp_mul_I]
  push_cast
  ring

private theorem norm_ofReal_mul_exp_mul_I {r : ℝ} (hr : 0 < r) (θ : ℝ) : ‖(r : ℂ) * cexp ((θ : ℂ) * I)‖ = r := by
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]

private theorem conj_ofReal_mul_exp_mul_I (r θ : ℝ) :
    starRingEnd ℂ ((r : ℂ) * cexp ((θ : ℂ) * I)) = (r : ℂ) * (cexp ((θ : ℂ) * I))⁻¹ := by
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg,
    Complex.exp_neg]

private theorem angular_cancel (k : ℤ) (θ : ℝ) :
    ((cexp ((θ : ℂ) * I))⁻¹) ^ k.toNat * cexp ((θ : ℂ) * I) ^ (-k).toNat * cexp ((θ : ℂ) * I) ^ k = 1 := by
  have he : cexp ((θ : ℂ) * I) ≠ 0 := Complex.exp_ne_zero _
  rw [inv_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_neg, ← zpow_add₀ he, ← zpow_add₀ he]
  rw [show -(k.toNat : ℤ) + ((-k).toNat : ℤ) + k = 0 by have := Int.toNat_sub_toNat_neg k; omega, zpow_zero]

private theorem testFun_mul_kerC_polar (k : ℤ) (w : ℂ) {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    complexTestFun k (Complex.polarCoord.symm (r, θ)) * kerC k w (Complex.polarCoord.symm (r, θ)) = rad k w r := by
  rw [polarCoord_symm_eq_mul_exp]
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  unfold complexTestFun kerC rad
  rw [norm_ofReal_mul_exp_mul_I hr, conj_ofReal_mul_exp_mul_I, mul_div_cancel_left₀ _ hr0]
  have hang := angular_cancel k θ
  calc ((r : ℂ) * (cexp ((θ : ℂ) * I))⁻¹) ^ k.toNat * ((r : ℂ) * cexp ((θ : ℂ) * I)) ^ (-k).toNat
          * cexp (-(2 * (Real.pi : ℂ) * (r : ℂ) ^ 2))
          * (cexp ((θ : ℂ) * I) ^ k * ((r ^ 2 : ℝ) : ℂ) ^ (w - 1))
        = (r : ℂ) ^ (k.toNat + (-k).toNat) * ((r ^ 2 : ℝ) : ℂ) ^ (w - 1) * cexp (-(2 * (Real.pi : ℂ) * (r : ℂ) ^ 2))
            * (((cexp ((θ : ℂ) * I))⁻¹) ^ k.toNat * cexp ((θ : ℂ) * I) ^ (-k).toNat * cexp ((θ : ℂ) * I) ^ k) := by
          rw [mul_pow, mul_pow, pow_add]; ring
      _ = _ := by rw [hang, mul_one, Int.toNat_add_toNat_neg_eq_natAbs]

private theorem ofReal_pow_eq_ofReal_sq_cpow {r : ℝ} (hr : 0 < r) (n : ℕ) :
    (r : ℂ) ^ n = ((r ^ 2 : ℝ) : ℂ) ^ ((n : ℂ) / 2) := by
  have h2 : (0 : ℝ) ≤ r ^ 2 := by positivity
  rw [show ((n : ℂ) / 2) = (((n : ℝ) / 2 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cpow h2, ← Complex.ofReal_pow]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hr.le]
  push_cast
  ring_nf

private theorem mellin_exp_neg_two_pi {s : ℂ} (hs : 0 < s.re) :
    mellin (fun t : ℝ => (Real.exp (-(2 * Real.pi) * t) : ℂ)) s = Gammaℂ s / 2 := by
  have h2s : 0 < (2 * s).re := by simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat]; linarith

  have h1 : mellin (fun t : ℝ => (Real.exp (-Real.pi * t) : ℂ)) s = Gammaℝ (2 * s) := by
    have h := hasSum_mellin_pi_mul_sq (ι := Unit) (a := fun _ => (1 : ℂ)) (r := fun _ => (1 : ℝ))
      (F := fun t : ℝ => (Real.exp (-Real.pi * t) : ℂ)) h2s ?_ ?_
    · have h' := h.tsum_eq
      rw [show (2 * s) / 2 = s by ring] at h'
      rw [← h']
      simp
    · intro t _; simp
    · exact (hasSum_fintype _).summable
  have h3 : (fun t : ℝ => (Real.exp (-(2 * Real.pi) * t) : ℂ))
      = fun t : ℝ => (Real.exp (-Real.pi * (2 * t)) : ℂ) := by
    funext t; congr 2; ring
  have h4 := mellin_comp_mul_left (fun u : ℝ => (Real.exp (-Real.pi * u) : ℂ)) s (by norm_num : (0 : ℝ) < 2)
  try simp only at h4
  rw [h3, h4, h1, Complex.Gammaℝ_def, Complex.Gammaℂ_def, smul_eq_mul, show -(2 * s) / 2 = -s by ring,
    show 2 * s / 2 = s by ring]
  have hprod : (2 * (Real.pi : ℂ)) ^ (-s) = ((2 : ℝ) : ℂ) ^ (-s) * (Real.pi : ℂ) ^ (-s) := by
    rw [← Complex.mul_cpow_ofReal_nonneg (by norm_num) Real.pi_pos.le]
    norm_num
  push_cast at hprod ⊢
  rw [hprod]
  ring

private theorem integral_rad {k : ℤ} {w : ℂ} (hw : 0 < w.re) :
    ∫ r in Ioi (0 : ℝ), (r : ℂ) * rad k w r = Gammaℂ (w + (k.natAbs : ℂ) / 2) / 4 := by
  set s : ℂ := w + (k.natAbs : ℂ) / 2 with hs_def
  have hs : 0 < s.re := by
    rw [hs_def, Complex.add_re, Complex.div_ofNat_re, Complex.natCast_re]; positivity
  have hmel := mellin_exp_neg_two_pi hs
  unfold mellin at hmel

  have hsub := integral_comp_rpow_Ioi (fun y : ℝ => (y : ℂ) ^ (s - 1) • (Real.exp (-(2 * Real.pi) * y) : ℂ))
    (by norm_num : (2 : ℝ) ≠ 0)
  simp only at hsub hmel
  rw [← hsub] at hmel

  have hint : ∀ r ∈ Ioi (0 : ℝ), (r : ℂ) * rad k w r
      = (1 / 2 : ℂ) * ((|(2 : ℝ)| * r ^ ((2 : ℝ) - 1)) •
          (((r ^ (2 : ℝ) : ℝ) : ℂ) ^ (s - 1) • (Real.exp (-(2 * Real.pi) * r ^ (2 : ℝ)) : ℂ))) := by
    intro r hr
    have hr : 0 < r := hr
    have hr2 : ((r ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (pow_pos hr 2).ne'
    have hexp : (Real.exp (-(2 * Real.pi) * r ^ 2) : ℂ) = cexp (-(2 * (Real.pi : ℂ) * (r : ℂ) ^ 2)) := by
      rw [Complex.ofReal_exp]; push_cast; congr 1; ring
    simp only [rad, smul_eq_mul, Complex.real_smul, Real.rpow_two, show ((2 : ℝ) - 1) = 1 by norm_num, Real.rpow_one,
      abs_two]
    rw [ofReal_pow_eq_ofReal_sq_cpow hr, ← Complex.cpow_add _ _ hr2,
      show (k.natAbs : ℂ) / 2 + (w - 1) = s - 1 by rw [hs_def]; ring, hexp]
    push_cast
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hint, integral_const_mul]
  convert congrArg (HMul.hMul (1 / 2 : ℂ)) hmel using 1 <;> try rfl
  ring

private theorem integral_Ioo_one : ∫ _θ in Ioo (-Real.pi) Real.pi, (1 : ℂ) = 2 * (Real.pi : ℂ) := by
  rw [setIntegral_const, measureReal_def, Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith [Real.pi_pos]),
    Complex.real_smul]
  push_cast
  ring

private theorem tateZetaC_complexTestFun' (k : ℤ) {w : ℂ} (hw : 0 < w.re) :
    tateZetaC (complexTestFun k) k w = (Real.pi / 2 : ℂ) * Gammaℂ (w + (k.natAbs : ℂ) / 2) := by
  rw [tateZetaC_eq_integral_ker, ← Complex.integral_comp_polarCoord_symm, polarCoord_target]
  have hint : ∀ p ∈ Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
      p.1 • (complexTestFun k (Complex.polarCoord.symm p) * kerC k w (Complex.polarCoord.symm p))
        = (p.1 : ℂ) * rad k w p.1 * 1 := by
    rintro ⟨r, θ⟩ ⟨hr, -⟩
    simp only [Complex.real_smul, mul_one]
    rw [testFun_mul_kerC_polar k w hr θ]
  have key := setIntegral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    (fun r : ℝ => (r : ℂ) * rad k w r) (fun _θ : ℝ => (1 : ℂ)) (Ioi 0) (Ioo (-Real.pi) Real.pi)
  try simp only at key
  rw [setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) hint, Measure.volume_eq_prod, key,
    integral_rad hw, integral_Ioo_one]
  ring

end

private theorem tateZetaC_complexTestFun (k : ℤ) {w : ℂ} (hw : 0 < w.re) :
    tateZetaC (complexTestFun k) k w = (Real.pi / 2 : ℂ) * Gammaℂ (w + (k.natAbs : ℂ) / 2) :=
  tateZetaC_complexTestFun' k hw

section
open Complex MeasureTheory LanglandsTunnell.TateLocal LanglandsTunnell.ArchPlace

private theorem continuous_psiComplex : Continuous psiComplex := by
  have h : psiComplex = fun z : ℂ => cexp (-(2 * (Real.pi : ℂ) * I * (z + starRingEnd ℂ z))) := by
    funext z; exact psiComplex_apply z
  rw [h]
  exact Complex.continuous_exp.comp ((continuous_const.mul (continuous_id.add Complex.continuous_conj)).neg)

private theorem norm_psiComplex (u : ℂ) : ‖psiComplex u‖ = 1 := by
  rw [psiComplex_apply, Complex.add_conj, Complex.norm_exp]
  have : (-(2 * (Real.pi : ℂ) * I * ((2 * u.re : ℝ) : ℂ))).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [this, Real.exp_zero]

private def phaseRate (v h : ℂ) : ℂ := -(2 * (Real.pi : ℂ) * I) * (v * h + starRingEnd ℂ (v * h))

private theorem psiComplex_line (v w h : ℂ) (t : ℝ) :
    psiComplex (v * (w + (t : ℂ) * h)) = psiComplex (v * w) * cexp ((t : ℂ) * phaseRate v h) := by
  rw [show v * (w + (t : ℂ) * h) = v * w + (t : ℂ) * (v * h) by ring, AddChar.map_add_eq_mul,
    psiComplex_apply ((t : ℂ) * (v * h))]
  congr 2
  rw [map_mul, Complex.conj_ofReal]
  unfold phaseRate
  ring

private theorem norm_phaseRate_le (v h : ℂ) : ‖phaseRate v h‖ ≤ 4 * Real.pi * (‖v‖ * ‖h‖) := by
  unfold phaseRate
  have h2 : ‖-(2 * (Real.pi : ℂ) * I)‖ = 2 * Real.pi := by
    rw [norm_neg, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
    simp
  rw [norm_mul, h2]
  have h3 : ‖v * h + starRingEnd ℂ (v * h)‖ ≤ 2 * (‖v‖ * ‖h‖) := by
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_conj, norm_mul]
    linarith
  nlinarith [Real.pi_pos, h3]

private theorem continuous_phaseRate (h : ℂ) : Continuous fun v : ℂ => phaseRate v h := by
  unfold phaseRate
  exact continuous_const.mul ((continuous_id.mul continuous_const).add
    (Complex.continuous_conj.comp (continuous_id.mul continuous_const)))

private theorem integrable_and_hasDerivAt_FC_line {f : ℂ → ℂ} (hf : Integrable f)
    (hvf : Integrable fun v : ℂ => ‖v‖ * ‖f v‖) (w h : ℂ) :
    Integrable (fun v : ℂ => f v * psiComplex (v * w) * phaseRate v h) ∧
      HasDerivAt (fun t : ℝ => FC f (w + (t : ℂ) * h)) (FC (fun v => phaseRate v h * f v) w) 0 := by
  have hψ : ∀ t : ℝ, AEStronglyMeasurable (fun v : ℂ => f v * psiComplex (v * (w + (t : ℂ) * h))) volume :=
    fun t => hf.aestronglyMeasurable.mul
      ((continuous_psiComplex.comp (continuous_id.mul continuous_const)).aestronglyMeasurable)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (volume : Measure ℂ)) (x₀ := (0 : ℝ))
    (F := fun (t : ℝ) (v : ℂ) => f v * psiComplex (v * (w + (t : ℂ) * h)))
    (F' := fun (t : ℝ) (v : ℂ) => f v * psiComplex (v * (w + (t : ℂ) * h)) * phaseRate v h)
    (bound := fun v : ℂ => 4 * Real.pi * ‖h‖ * (‖v‖ * ‖f v‖)) Filter.univ_mem
    (Filter.Eventually.of_forall hψ) ?_ ((hψ 0).mul (continuous_phaseRate h).aestronglyMeasurable) ?_
    (hvf.const_mul _) ?_
  · refine ⟨?_, ?_⟩
    · have h1 := key.1
      simpa only [Complex.ofReal_zero, zero_mul, add_zero] using h1
    · have h2 := key.2
      convert h2 using 1 <;> try rfl
      show (∫ v : ℂ, phaseRate v h * f v * psiComplex (v * w)) = _
      simp only [Complex.ofReal_zero, zero_mul, add_zero]
      congr 1
      funext v
      ring
  ·
    refine hf.norm.mono' (hψ 0) (Filter.Eventually.of_forall fun v => ?_)
    rw [norm_mul, norm_psiComplex, mul_one]
  ·
    refine Filter.Eventually.of_forall fun v t _ => ?_
    rw [norm_mul, norm_mul, norm_psiComplex, mul_one]
    have := norm_phaseRate_le v h
    calc ‖f v‖ * ‖phaseRate v h‖ ≤ ‖f v‖ * (4 * Real.pi * (‖v‖ * ‖h‖)) :=
          mul_le_mul_of_nonneg_left this (norm_nonneg _)
      _ = 4 * Real.pi * ‖h‖ * (‖v‖ * ‖f v‖) := by ring
  ·
    refine Filter.Eventually.of_forall fun v t _ => ?_
    have hfun : (fun t : ℝ => f v * psiComplex (v * (w + (t : ℂ) * h)))
        = fun t : ℝ => f v * psiComplex (v * w) * cexp ((t : ℂ) * phaseRate v h) := by
      funext t; rw [psiComplex_line]; ring
    beta_reduce
    rw [hfun, psiComplex_line]
    have hd : HasDerivAt (fun t : ℝ => cexp ((t : ℂ) * phaseRate v h))
        (cexp ((t : ℂ) * phaseRate v h) * phaseRate v h) t := by
      have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) * phaseRate v h) (phaseRate v h) t := by
        simpa using ((hasDerivAt_id t).ofReal_comp).mul_const (phaseRate v h)
      simpa using h1.cexp
    convert hd.const_mul (f v * psiComplex (v * w)) using 1 <;> try rfl
    ring

private theorem hasDerivAt_FC_line
    {f : ℂ → ℂ} (hf : Integrable f) (hvf : Integrable fun v : ℂ => ‖v‖ * ‖f v‖) (w h : ℂ) :
    HasDerivAt (fun t : ℝ => FC f (w + (t : ℂ) * h)) (FC (fun v => phaseRate v h * f v) w) 0 :=
  (integrable_and_hasDerivAt_FC_line hf hvf w h).2

private theorem deriv_FC_line {f : ℂ → ℂ} (hf : Integrable f) (hvf : Integrable fun v : ℂ => ‖v‖ * ‖f v‖) (w h : ℂ) :
    deriv (fun t : ℝ => FC f (w + (t : ℂ) * h)) 0 = FC (fun v => phaseRate v h * f v) w :=
  (hasDerivAt_FC_line hf hvf w h).deriv

private theorem integrable_phaseRate_mul {f : ℂ → ℂ} (hf : Integrable f) (hvf : Integrable fun v : ℂ => ‖v‖ * ‖f v‖)
    (w h : ℂ) : Integrable fun v : ℂ => phaseRate v h * f v * psiComplex (v * w) := by
  have := (integrable_and_hasDerivAt_FC_line hf hvf w h).1
  refine this.congr (Filter.Eventually.of_forall fun v => ?_)
  ring

private theorem phaseRate_one (v : ℂ) : phaseRate v 1 = -(2 * (Real.pi : ℂ) * I) * (v + starRingEnd ℂ v) := by
  simp [phaseRate]

private theorem phaseRate_I (v : ℂ) : phaseRate v I = -(2 * (Real.pi : ℂ) * I) * (v * I - starRingEnd ℂ v * I) := by
  simp only [phaseRate, map_mul, Complex.conj_I]
  ring

private theorem phaseRate_neg (v h : ℂ) : phaseRate v (-h) = -phaseRate v h := by
  simp only [phaseRate, mul_neg, map_neg]
  ring

private theorem neg_four_pi_I_mul_FC_mul_left {f : ℂ → ℂ} (hf : Integrable f)
    (hvf : Integrable fun v : ℂ => ‖v‖ * ‖f v‖) (w : ℂ) :
    -(4 * (Real.pi : ℂ) * I) * FC (fun v => v * f v) w
      = deriv (fun t : ℝ => FC f (w + (t : ℂ) * 1)) 0 - I * deriv (fun t : ℝ => FC f (w + (t : ℂ) * I)) 0 := by
  rw [deriv_FC_line hf hvf w 1, deriv_FC_line hf hvf w I]
  show -(4 * (Real.pi : ℂ) * I) * (∫ v : ℂ, v * f v * psiComplex (v * w))
    = (∫ v : ℂ, phaseRate v 1 * f v * psiComplex (v * w)) - I * ∫ v : ℂ, phaseRate v I * f v * psiComplex (v * w)
  rw [← integral_const_mul, ← integral_const_mul, ← integral_sub (integrable_phaseRate_mul hf hvf w 1)
    ((integrable_phaseRate_mul hf hvf w I).const_mul I)]
  congr 1
  funext v
  rw [phaseRate_one, phaseRate_I]
  linear_combination (-(2 * (Real.pi : ℂ) * I * (v - starRingEnd ℂ v) * f v * psiComplex (v * w))) * Complex.I_sq

private theorem neg_four_pi_I_mul_FC_conj_mul_left {f : ℂ → ℂ} (hf : Integrable f)
    (hvf : Integrable fun v : ℂ => ‖v‖ * ‖f v‖) (w : ℂ) :
    -(4 * (Real.pi : ℂ) * I) * FC (fun v => starRingEnd ℂ v * f v) w
      = deriv (fun t : ℝ => FC f (w + (t : ℂ) * 1)) 0 + I * deriv (fun t : ℝ => FC f (w + (t : ℂ) * I)) 0 := by
  rw [deriv_FC_line hf hvf w 1, deriv_FC_line hf hvf w I]
  show -(4 * (Real.pi : ℂ) * I) * (∫ v : ℂ, starRingEnd ℂ v * f v * psiComplex (v * w))
    = (∫ v : ℂ, phaseRate v 1 * f v * psiComplex (v * w)) + I * ∫ v : ℂ, phaseRate v I * f v * psiComplex (v * w)
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (integrable_phaseRate_mul hf hvf w 1)
    ((integrable_phaseRate_mul hf hvf w I).const_mul I)]
  congr 1
  funext v
  rw [phaseRate_one, phaseRate_I]
  linear_combination (2 * (Real.pi : ℂ) * I * (v - starRingEnd ℂ v) * f v * psiComplex (v * w)) * Complex.I_sq

private theorem four_pi_I_ne_zero : (4 * (Real.pi : ℂ) * I) ≠ 0 := by
  have : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_pos.ne'
  exact mul_ne_zero (mul_ne_zero (by norm_num) this) Complex.I_ne_zero

private theorem FC_mul_left_eq {f : ℂ → ℂ} (hf : Integrable f) (hvf : Integrable fun v : ℂ => ‖v‖ * ‖f v‖) (w : ℂ) :
    FC (fun v => v * f v) w
      = (deriv (fun t : ℝ => FC f (w + (t : ℂ) * 1)) 0 - I * deriv (fun t : ℝ => FC f (w + (t : ℂ) * I)) 0)
          / (-(4 * (Real.pi : ℂ) * I)) := by
  rw [← neg_four_pi_I_mul_FC_mul_left hf hvf w, mul_div_cancel_left₀ _ (neg_ne_zero.2 four_pi_I_ne_zero)]

private theorem FC_conj_mul_left_eq
    {f : ℂ → ℂ} (hf : Integrable f) (hvf : Integrable fun v : ℂ => ‖v‖ * ‖f v‖) (w : ℂ) :
    FC (fun v => starRingEnd ℂ v * f v) w
      = (deriv (fun t : ℝ => FC f (w + (t : ℂ) * 1)) 0 + I * deriv (fun t : ℝ => FC f (w + (t : ℂ) * I)) 0)
          / (-(4 * (Real.pi : ℂ) * I)) := by
  rw [← neg_four_pi_I_mul_FC_conj_mul_left hf hvf w, mul_div_cancel_left₀ _ (neg_ne_zero.2 four_pi_I_ne_zero)]

private theorem conj_line_one (ξ : ℂ) (t : ℝ) : starRingEnd ℂ (ξ + (t : ℂ) * 1) = starRingEnd ℂ ξ + (t : ℂ) * 1 := by
  simp [Complex.conj_ofReal]

private theorem conj_line_I (ξ : ℂ) (t : ℝ) : starRingEnd ℂ (ξ + (t : ℂ) * I) = starRingEnd ℂ ξ + (t : ℂ) * (-I) := by
  simp [Complex.conj_ofReal]

private theorem deriv_FC_conj_line_I
    {f : ℂ → ℂ} (hf : Integrable f) (hvf : Integrable fun v : ℂ => ‖v‖ * ‖f v‖) (ξ : ℂ) :
    deriv (fun t : ℝ => FC f (starRingEnd ℂ (ξ + (t : ℂ) * I))) 0
      = -deriv (fun t : ℝ => FC f (starRingEnd ℂ ξ + (t : ℂ) * I)) 0 := by
  simp only [conj_line_I]
  rw [deriv_FC_line hf hvf _ (-I), deriv_FC_line hf hvf _ I]
  show (∫ v : ℂ, phaseRate v (-I) * f v * psiComplex (v * starRingEnd ℂ ξ))
    = -∫ v : ℂ, phaseRate v I * f v * psiComplex (v * starRingEnd ℂ ξ)
  rw [← integral_neg]
  congr 1
  funext v
  rw [phaseRate_neg]
  ring

private theorem neg_four_pi_I_mul_FC_mul_left_conj {f : ℂ → ℂ} (hf : Integrable f)
    (hvf : Integrable fun v : ℂ => ‖v‖ * ‖f v‖) (ξ : ℂ) :
    -(4 * (Real.pi : ℂ) * I) * FC (fun v => v * f v) (starRingEnd ℂ ξ)
      = deriv (fun t : ℝ => FC f (starRingEnd ℂ (ξ + (t : ℂ) * 1))) 0
          + I * deriv (fun t : ℝ => FC f (starRingEnd ℂ (ξ + (t : ℂ) * I))) 0 := by
  simp only [conj_line_one]
  rw [deriv_FC_conj_line_I hf hvf ξ, neg_four_pi_I_mul_FC_mul_left hf hvf]
  ring

private theorem neg_four_pi_I_mul_FC_conj_mul_left_conj {f : ℂ → ℂ} (hf : Integrable f)
    (hvf : Integrable fun v : ℂ => ‖v‖ * ‖f v‖) (ξ : ℂ) :
    -(4 * (Real.pi : ℂ) * I) * FC (fun v => starRingEnd ℂ v * f v) (starRingEnd ℂ ξ)
      = deriv (fun t : ℝ => FC f (starRingEnd ℂ (ξ + (t : ℂ) * 1))) 0
          - I * deriv (fun t : ℝ => FC f (starRingEnd ℂ (ξ + (t : ℂ) * I))) 0 := by
  simp only [conj_line_one]
  rw [deriv_FC_conj_line_I hf hvf ξ, neg_four_pi_I_mul_FC_conj_mul_left hf hvf]
  ring

end

section
open Complex MeasureTheory LanglandsTunnell.TateLocal LanglandsTunnell.ArchPlace

private def testExp (z : ℂ) : ℂ := cexp (-(2 * (Real.pi : ℂ) * ((‖z‖ : ℝ) : ℂ) ^ 2))

private theorem testExp_eq (z : ℂ) : testExp z = cexp (-(2 * (Real.pi : ℂ) * (z * starRingEnd ℂ z))) := by
  simp [testExp, Complex.mul_conj, Complex.normSq_eq_norm_sq]

private def stdConj (n : ℕ) (z : ℂ) : ℂ := starRingEnd ℂ z ^ n * testExp z

private def stdPow (n : ℕ) (z : ℂ) : ℂ := z ^ n * testExp z

private theorem complexTestFun_natCast (n : ℕ) : complexTestFun (n : ℤ) = stdConj n := by
  funext z
  simp [complexTestFun, stdConj, testExp]

private theorem complexTestFun_neg_natCast (n : ℕ) : complexTestFun (-(n : ℤ)) = stdPow n := by
  funext z
  simp [complexTestFun, stdPow, testExp]

private theorem stdConj_succ (n : ℕ) : stdConj (n + 1) = fun v : ℂ => starRingEnd ℂ v * stdConj n v := by
  funext v
  simp only [stdConj, pow_succ]
  ring

private theorem stdPow_succ (n : ℕ) : stdPow (n + 1) = fun v : ℂ => v * stdPow n v := by
  funext v
  simp only [stdPow, pow_succ]
  ring

private theorem kerC_zero_one (z : ℂ) : kerC 0 1 z = 1 := by
  simp [kerC]

private theorem IsGaussPolyC.integrable_of_mem {f : ℂ → ℂ} (hf : IsGaussPolyC f) : Integrable f := by
  have h := integrable_tateC' hf 0 (w := 1) (by norm_num)
  simpa only [kerC_zero_one, mul_one] using h

private theorem IsGaussPolyC.mul_left_z {f : ℂ → ℂ} (hf : IsGaussPolyC f) : IsGaussPolyC fun z : ℂ => z * f z := by
  obtain ⟨p, α, β₁, β₂, hα, rfl⟩ := hf
  refine ⟨MvPolynomial.X 0 * p, α, β₁, β₂, hα, ?_⟩
  funext z
  simp only [gaussPolyC, map_mul, MvPolynomial.eval_X, Matrix.cons_val_zero]
  ring

private theorem IsGaussPolyC.mul_left_conj {f : ℂ → ℂ} (hf : IsGaussPolyC f) :
    IsGaussPolyC fun z : ℂ => starRingEnd ℂ z * f z := by
  obtain ⟨p, α, β₁, β₂, hα, rfl⟩ := hf
  refine ⟨MvPolynomial.X 1 * p, α, β₁, β₂, hα, ?_⟩
  funext z
  simp only [gaussPolyC, map_mul, MvPolynomial.eval_X, Matrix.cons_val_one, Matrix.cons_val_zero]
  ring

private theorem IsGaussPolyC.integrable_norm_mul {f : ℂ → ℂ} (hf : IsGaussPolyC f) :
    Integrable fun v : ℂ => ‖v‖ * ‖f v‖ := by
  have h := hf.mul_left_z.integrable_of_mem.norm
  refine h.congr (Filter.Eventually.of_forall fun v => ?_)
  simp

private theorem isGaussPolyC_stdConj (n : ℕ) : IsGaussPolyC (stdConj n) := by
  rw [← complexTestFun_natCast]; exact isGaussPolyC_complexTestFun' _

private theorem isGaussPolyC_stdPow (n : ℕ) : IsGaussPolyC (stdPow n) := by
  rw [← complexTestFun_neg_natCast]; exact isGaussPolyC_complexTestFun' _

private theorem hasDerivAt_line (w h : ℂ) : HasDerivAt (fun t : ℝ => w + (t : ℂ) * h) h 0 := by
  simpa using (((hasDerivAt_id (0 : ℝ)).ofReal_comp).mul_const h).const_add w

private theorem conj_line (w h : ℂ) (t : ℝ) :
    starRingEnd ℂ (w + (t : ℂ) * h) = starRingEnd ℂ w + (t : ℂ) * starRingEnd ℂ h := by
  rw [map_add, map_mul, Complex.conj_ofReal]

private theorem hasDerivAt_testExp_line (w h : ℂ) :
    HasDerivAt (fun t : ℝ => testExp (w + (t : ℂ) * h))
      (cexp (-(2 * (Real.pi : ℂ) * (w * starRingEnd ℂ w)))
        * -(2 * (Real.pi : ℂ) * (h * starRingEnd ℂ w + w * starRingEnd ℂ h))) 0 := by
  have hfun : (fun t : ℝ => testExp (w + (t : ℂ) * h))
      = fun t : ℝ =>
          cexp (-(2 * (Real.pi : ℂ) * ((w + (t : ℂ) * h) * (starRingEnd ℂ w + (t : ℂ) * starRingEnd ℂ h)))) := by
    funext t; rw [testExp_eq, conj_line]
  rw [hfun]
  simpa using ((((hasDerivAt_line w h).mul (hasDerivAt_line (starRingEnd ℂ w) (starRingEnd ℂ h))).const_mul
    (2 * (Real.pi : ℂ))).neg).cexp

private theorem deriv_stdPow_line (n : ℕ) (c w h : ℂ) :
    deriv (fun t : ℝ => c * stdPow n (w + (t : ℂ) * h)) 0
      = c * ((n : ℂ) * w ^ (n - 1) * h * testExp w
          + w ^ n * (cexp (-(2 * (Real.pi : ℂ) * (w * starRingEnd ℂ w)))
              * -(2 * (Real.pi : ℂ) * (h * starRingEnd ℂ w + w * starRingEnd ℂ h)))) := by
  have hp : HasDerivAt (fun t : ℝ => (w + (t : ℂ) * h) ^ n) ((n : ℂ) * w ^ (n - 1) * h) 0 := by
    first | simpa using (hasDerivAt_line w h).pow n | (have h' := (hasDerivAt_line w h).pow n; simp at h'; exact h') | exact (hasDerivAt_line w h).pow n
  have hd := (hp.mul (hasDerivAt_testExp_line w h)).const_mul c
  refine HasDerivAt.deriv ?_
  simpa [stdPow] using hd

private theorem deriv_stdConj_line (n : ℕ) (c w h : ℂ) :
    deriv (fun t : ℝ => c * stdConj n (w + (t : ℂ) * h)) 0
      = c * ((n : ℂ) * starRingEnd ℂ w ^ (n - 1) * starRingEnd ℂ h * testExp w
          + starRingEnd ℂ w ^ n * (cexp (-(2 * (Real.pi : ℂ) * (w * starRingEnd ℂ w)))
              * -(2 * (Real.pi : ℂ) * (h * starRingEnd ℂ w + w * starRingEnd ℂ h)))) := by
  have hfun : (fun t : ℝ => c * stdConj n (w + (t : ℂ) * h))
      = fun t : ℝ => c * ((starRingEnd ℂ w + (t : ℂ) * starRingEnd ℂ h) ^ n * testExp (w + (t : ℂ) * h)) := by
    funext t; simp only [stdConj, conj_line]
  have hp : HasDerivAt (fun t : ℝ => (starRingEnd ℂ w + (t : ℂ) * starRingEnd ℂ h) ^ n)
      ((n : ℂ) * starRingEnd ℂ w ^ (n - 1) * starRingEnd ℂ h) 0 := by
    first | simpa using (hasDerivAt_line (starRingEnd ℂ w) (starRingEnd ℂ h)).pow n | (have h' := (hasDerivAt_line (starRingEnd ℂ w) (starRingEnd ℂ h)).pow n; simp at h'; exact h') | exact (hasDerivAt_line (starRingEnd ℂ w) (starRingEnd ℂ h)).pow n
  have hd := (hp.mul (hasDerivAt_testExp_line w h)).const_mul c
  rw [hfun]
  refine HasDerivAt.deriv ?_
  simpa using hd

private theorem FC_stdConj_zero : FC (stdConj 0) = fun w : ℂ => (1 / 2 : ℂ) * stdPow 0 w := by
  have h := tateFourier_complexTestFun_zero_self
  have h2 : ∀ w : ℂ, tateFourier psiComplex ((2 : ENNReal) • volume) (complexTestFun 0) w
      = 2 * FC (complexTestFun 0) w := by
    intro w
    show (∫ x : ℂ, complexTestFun 0 x * psiComplex (x * w) ∂((2 : ENNReal) • volume))
      = 2 * ∫ x : ℂ, complexTestFun 0 x * psiComplex (x * w)
    rw [integral_smul_measure]
    simp
  funext w
  have h3 := congrFun h w
  rw [h2 w] at h3
  have h0 : stdConj 0 = complexTestFun 0 := by rw [← complexTestFun_natCast]; rfl
  have h0' : stdPow 0 w = complexTestFun 0 w := by rw [← complexTestFun_neg_natCast]; rfl
  rw [h0, h0']
  linear_combination (1 / 2 : ℂ) * h3

private theorem FC_stdPow_zero : FC (stdPow 0) = fun w : ℂ => (1 / 2 : ℂ) * stdConj 0 w := by
  have h0 : stdPow 0 = stdConj 0 := by funext z; simp [stdPow, stdConj]
  rw [h0, FC_stdConj_zero]
  funext w
  simp [stdPow, stdConj]

private theorem FC_stdConj (n : ℕ) : FC (stdConj n) = fun w : ℂ => ((-I) ^ n / 2) * stdPow n w := by
  induction n with
  | zero => simpa using FC_stdConj_zero
  | succ n ih =>
    funext w
    have hf := (isGaussPolyC_stdConj n).integrable_of_mem
    have hvf := (isGaussPolyC_stdConj n).integrable_norm_mul
    have hr := neg_four_pi_I_mul_FC_conj_mul_left hf hvf w
    rw [← stdConj_succ, ih] at hr
    simp only at hr
    rw [deriv_stdPow_line n _ w 1, deriv_stdPow_line n _ w I, map_one, Complex.conj_I, ← testExp_eq] at hr
    refine mul_left_cancel₀ (neg_ne_zero.2 four_pi_I_ne_zero) ?_
    rw [hr, stdPow]
    linear_combination (-(testExp w * ((-I) ^ n / 2) * (-((n : ℂ) * w ^ (n - 1)) + 2 * (Real.pi : ℂ) * w ^ n * w
      + 2 * (Real.pi : ℂ) * w ^ n * starRingEnd ℂ w))) * Complex.I_sq

private theorem FC_stdPow (n : ℕ) : FC (stdPow n) = fun w : ℂ => ((-I) ^ n / 2) * stdConj n w := by
  induction n with
  | zero => simpa using FC_stdPow_zero
  | succ n ih =>
    funext w
    have hf := (isGaussPolyC_stdPow n).integrable_of_mem
    have hvf := (isGaussPolyC_stdPow n).integrable_norm_mul
    have hr := neg_four_pi_I_mul_FC_mul_left hf hvf w
    rw [← stdPow_succ, ih] at hr
    simp only at hr
    rw [deriv_stdConj_line n _ w 1, deriv_stdConj_line n _ w I, map_one, Complex.conj_I, ← testExp_eq] at hr
    refine mul_left_cancel₀ (neg_ne_zero.2 four_pi_I_ne_zero) ?_
    rw [hr, stdConj]
    linear_combination (-(testExp w * ((-I) ^ n / 2) * (-((n : ℂ) * starRingEnd ℂ w ^ (n - 1))
      + 2 * (Real.pi : ℂ) * starRingEnd ℂ w ^ n * w + 2 * (Real.pi : ℂ) * starRingEnd ℂ w ^ n * starRingEnd ℂ w)))
      * Complex.I_sq

private theorem FC_complexTestFun' (k : ℤ) : FC (complexTestFun k) = fun w : ℂ => cC k * complexTestFun (-k) w := by
  obtain ⟨n, rfl | rfl⟩ := k.eq_nat_or_neg
  · rw [complexTestFun_natCast, FC_stdConj, ← complexTestFun_neg_natCast]
    funext w
    simp [cC]
  · rw [complexTestFun_neg_natCast, FC_stdPow, neg_neg, complexTestFun_natCast]
    funext w
    simp [cC]

private theorem FC_complexTestFun_one : FC (complexTestFun 1) = fun w : ℂ => (-I / 2) * complexTestFun (-1) w := by
  rw [FC_complexTestFun']
  simp [cC]

private theorem FC_complexTestFun_neg_one : FC (complexTestFun (-1)) = fun w : ℂ => (-I / 2) * complexTestFun 1 w := by
  rw [FC_complexTestFun']
  simp [cC]

end

private theorem FC_complexTestFun (k : ℤ) :
    FC (complexTestFun k) = fun w : ℂ => cC k * complexTestFun (-k) w :=
  FC_complexTestFun' k

section
open Complex MeasureTheory LanglandsTunnell.TateLocal LanglandsTunnell.ArchPlace
open scoped NNReal ENNReal

private theorem modulus_C_cast (z : ℂ) : ((modulus z : ℝ) : ℂ) = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [modulus_complex_eq_nnnorm_sq]; push_cast; rfl

private theorem measurable_modulus_inv_ennreal_C : Measurable fun z : ℂ => ((modulus z : ℝ≥0∞))⁻¹ := by
  simp_rw [modulus_complex_eq_nnnorm_sq]
  exact (measurable_nnnorm.pow_const 2).coe_nnreal_ennreal.inv

private theorem aemeasurable_modulus_inv_C :
    AEMeasurable (fun z : ℂ => (modulus z)⁻¹) ((volume : Measure ℂ).restrict {0}ᶜ) := by
  simp_rw [modulus_complex_eq_nnnorm_sq]
  exact (measurable_nnnorm.pow_const 2).inv.aemeasurable

private theorem ae_modulus_inv_lt_top_C : ∀ᵐ z ∂(volume : Measure ℂ), ((modulus z : ℝ≥0∞))⁻¹ < ⊤ := by
  filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0 : ℂ))] with z hz
  have hz0 : z ≠ 0 := hz
  rw [modulus_complex_eq_nnnorm_sq]
  exact ENNReal.inv_lt_top.mpr (by simpa using ENNReal.pow_pos (ENNReal.coe_pos.2 (nnnorm_pos.2 hz0)) 2)

private theorem modulus_inv_toReal_C (z : ℂ) : (((modulus z : ℝ≥0∞))⁻¹).toReal = (‖z‖ ^ 2)⁻¹ := by
  rw [modulus_complex_eq_nnnorm_sq, ENNReal.toReal_inv]; simp

private theorem mulMeasure_volume_eq_C :
    mulMeasure (volume : Measure ℂ) = (volume : Measure ℂ).withDensity fun z => ((modulus z : ℝ≥0∞))⁻¹ := by
  unfold mulMeasure
  have hres : (volume : Measure ℂ).restrict ({0}ᶜ : Set ℂ) = volume :=
    Measure.restrict_eq_self_of_ae_mem (compl_mem_ae_iff.mpr (measure_singleton (0 : ℂ)))
  rw [hres]

private theorem integrable_mulMeasure_iff_C {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {h : ℂ → E} :
    Integrable h (mulMeasure (volume : Measure ℂ)) ↔ Integrable (fun z : ℂ => (‖z‖ ^ 2)⁻¹ • h z) volume := by
  rw [mulMeasure_volume_eq_C, integrable_withDensity_iff_integrable_smul' measurable_modulus_inv_ennreal_C
    ae_modulus_inv_lt_top_C]
  simp_rw [modulus_inv_toReal_C]

private theorem integrable_mulMeasure_iff_complex_C {h : ℂ → ℂ} :
    Integrable h (mulMeasure (volume : Measure ℂ))
      ↔ Integrable (fun z : ℂ => (((‖z‖ ^ 2)⁻¹ : ℝ) : ℂ) * h z) volume :=
  integrable_mulMeasure_iff_C

private theorem sfinite_mulMeasure_C : SFinite (mulMeasure (volume : Measure ℂ)) := by
  rw [mulMeasure_volume_eq_C]; infer_instance

private theorem integral_mulMeasure_C (h : ℂ → ℝ) :
    ∫ z, h z ∂(mulMeasure (volume : Measure ℂ)) = ∫ z : ℂ, (‖z‖ ^ 2)⁻¹ * h z := by
  rw [mulMeasure_volume_eq_C, integral_withDensity_eq_integral_toReal_smul measurable_modulus_inv_ennreal_C
    ae_modulus_inv_lt_top_C]
  simp_rw [modulus_inv_toReal_C, smul_eq_mul]

private theorem charExt_complexCharFun (k : ℤ) {z : ℂ} (hz : z ≠ 0) :
    charExt (complexCharFun 0 k) z = (z / ((‖z‖ : ℝ) : ℂ)) ^ k := by
  rw [charExt_of_ne_zero _ hz, complexCharFun_apply]
  simp [anglePhase]

private theorem norm_charExt_complexCharFun (k : ℤ) {z : ℂ} (hz : z ≠ 0) : ‖charExt (complexCharFun 0 k) z‖ = 1 := by
  rw [charExt_complexCharFun k hz, norm_zpow, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm,
    div_self (norm_ne_zero_iff.2 hz), one_zpow]

private theorem charExt_complexCharFun_eq_ite (k : ℤ) :
    charExt (complexCharFun 0 k) = fun z : ℂ => if z = 0 then 0 else (z / ((‖z‖ : ℝ) : ℂ)) ^ k := by
  funext z
  split_ifs with hz
  · subst hz; simp
  · exact charExt_complexCharFun k hz

private theorem measurable_charExt_complexCharFun (k : ℤ) : Measurable (charExt (complexCharFun 0 k)) := by
  rw [charExt_complexCharFun_eq_ite]
  exact Measurable.ite (by simp) measurable_const
    ((measurable_id.div (Complex.measurable_ofReal.comp measurable_norm)).pow_const k)

private theorem complexCharFun_zero_inv (k : ℤ) : (complexCharFun 0 k)⁻¹ = complexCharFun 0 (-k) := by
  refine MonoidHom.ext fun x => ?_
  rw [MonoidHom.inv_apply]
  refine inv_eq_of_mul_eq_one_left (Units.ext ?_)
  rw [Units.val_mul, complexCharFun_apply, complexCharFun_apply, Units.val_one]
  simp [zpow_neg]
  exact inv_mul_cancel₀ (zpow_ne_zero k (anglePhase_ne_zero x))

private theorem ofReal_sq_cpow {r : ℝ} (hr : 0 < r) (w : ℂ) : ((r ^ 2 : ℝ) : ℂ) ^ w = (r : ℂ) ^ (2 * w) := by
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  rw [sq, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hr.le hr.le, ← Complex.cpow_add _ _ hr', two_mul]

private theorem complexZeta_eq_tateZetaC (f : ℂ → ℂ) (k : ℤ) (w : ℂ) :
    complexZeta volume f (complexCharFun 0 k) w = tateZetaC f k w := by
  unfold complexZeta tateZetaC
  refine integral_congr_ae ?_
  filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0 : ℂ))] with z hz
  have hz0 : z ≠ 0 := hz
  rw [charExt_complexCharFun k hz0]
  unfold kerC
  rw [ofReal_sq_cpow (norm_pos_iff.2 hz0), show (2 : ℂ) * (w - 1) = 2 * w - 2 by ring]
  ring

private theorem tateZetaC_eq_localZeta (f : ℂ → ℂ) (k : ℤ) (w : ℂ) :
    tateZetaC f k w = localZeta volume f (complexCharFun 0 k) w := by
  rw [← complexZeta_eq_tateZetaC, complexZeta_eq_localZeta]

private theorem tateFourier_psiComplex (f : ℂ → ℂ) : tateFourier psiComplex volume f = FC f := rfl

private theorem IsGaussPolyC.continuous {f : ℂ → ℂ} (hf : IsGaussPolyC f) : Continuous f := by
  obtain ⟨p, α, β₁, β₂, -, rfl⟩ := hf
  unfold gaussPolyC
  refine Continuous.mul ?_ (Complex.continuous_exp.comp ?_)
  · exact p.continuous_eval.comp (by fun_prop)
  · fun_prop

private theorem IsGaussPolyC.comp_mul_left {f : ℂ → ℂ} (hf : IsGaussPolyC f) {c : ℂ} (hc : c ≠ 0) :
    IsGaussPolyC fun z : ℂ => f (c * z) := by
  obtain ⟨p, α, β₁, β₂, hα, rfl⟩ := hf
  refine ⟨MvPolynomial.bind₁ ![MvPolynomial.C c * MvPolynomial.X 0,
      MvPolynomial.C (starRingEnd ℂ c) * MvPolynomial.X 1] p,
    α * ‖c‖ ^ 2, β₁ * c, β₂ * starRingEnd ℂ c, mul_pos hα (pow_pos (norm_pos_iff.2 hc) 2), ?_⟩
  funext z
  simp only [gaussPolyC]
  congr 1
  · rw [MvPolynomial.eval, MvPolynomial.eval, MvPolynomial.eval₂Hom_bind₁]
    refine congrArg (fun v : Fin 2 → ℂ => MvPolynomial.eval₂Hom (RingHom.id ℂ) v p) ?_
    funext i
    fin_cases i <;> simp
  · congr 1
    rw [norm_mul, map_mul]
    push_cast
    ring

private theorem integrable_kernel_C {f g : ℂ → ℂ} (hf : IsGaussPolyC f) (hg : IsGaussPolyC g) (x : ℂ) :
    Integrable (fun p : ℂ × ℂ => f p.1 * g p.2 * (psiComplex (p.1 * p.2 * x) : ℂ))
      ((volume : Measure ℂ).prod volume) := by
  refine (hf.integrable_of_mem.mul_prod hg.integrable_of_mem).mul_bdd (c := 1) ?_
    (Filter.Eventually.of_forall fun p => ?_)
  · exact (continuous_psiComplex.comp (by fun_prop)).aestronglyMeasurable
  · exact (norm_psiComplex _).le

private theorem integral_comp_mul_left_C {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] (N : ℂ → G) (y : ℂ) :
    ∫ x : ℂ, N (y * x) = (‖y‖ ^ 2)⁻¹ • ∫ t : ℂ, N t := by
  have hrot : ∀ x : ℂ, y * x = ‖y‖ • (rotation (Circle.exp (arg y)) x) := by
    intro x
    rw [rotation_apply, Circle.coe_exp, Complex.real_smul, ← mul_assoc, norm_mul_exp_arg_mul_I]
  simp_rw [hrot]
  rw [(rotation (Circle.exp (arg y))).measurePreserving.integral_comp
      (rotation (Circle.exp (arg y))).toHomeomorph.measurableEmbedding (fun v : ℂ => N (‖y‖ • v)),
    Measure.integral_comp_smul volume N ‖y‖, finrank_real_complex,
    abs_of_nonneg (inv_nonneg.2 (pow_nonneg (norm_nonneg y) 2))]

private theorem integral_comp_mul_left_C_real (N : ℂ → ℝ) (y : ℂ) :
    ∫ x : ℂ, N (y * x) = (‖y‖ ^ 2)⁻¹ * ∫ t : ℂ, N t := by
  rw [integral_comp_mul_left_C, smul_eq_mul]

private theorem integrable_slice_C {F : ℂ → ℂ} (hF : IsGaussPolyC F) (k : ℤ) {s : ℂ} (hs₁ : s.re < 1) (c : ℂ) {y : ℂ}
    (hy : y ≠ 0) :
    Integrable (fun x : ℂ => c * F (y * x) * (charExt (complexCharFun 0 k) x * ((‖x‖ ^ 2 : ℝ) : ℂ) ^ (1 - s)))
      (mulMeasure (volume : Measure ℂ)) := by
  rw [integrable_mulMeasure_iff_complex_C]
  have h1s : 0 < (1 - s).re := by simp; linarith
  have hint := (integrable_tateC' (hF.comp_mul_left hy) k h1s).const_mul c
  refine hint.congr ?_
  filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0 : ℂ))] with x hx
  have hx0 : x ≠ 0 := hx
  have hm : ((‖x‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (pow_pos (norm_pos_iff.2 hx0) 2).ne'
  rw [charExt_complexCharFun k hx0]
  unfold kerC
  rw [Complex.cpow_sub _ _ hm, Complex.cpow_one]
  push_cast
  field_simp

private theorem integral_norm_slice_C (u F : ℂ → ℂ) (k : ℤ) (s : ℂ) {y : ℂ} (hy : y ≠ 0) :
    (∫ x, ‖u y * ((‖y‖ ^ 2 : ℝ) : ℂ) * F (y * x) * (charExt (complexCharFun 0 k) x * ((‖x‖ ^ 2 : ℝ) : ℂ) ^ (1 - s))‖
        ∂(mulMeasure (volume : Measure ℂ)))
      = ‖u y‖ * (‖y‖ ^ 2) ^ s.re * ∫ t : ℂ, ‖F t‖ * (‖t‖ ^ 2) ^ (-s.re) := by
  have hmy : 0 < ‖y‖ ^ 2 := pow_pos (norm_pos_iff.2 hy) 2
  have hmy' : (‖y‖ ^ 2) ^ s.re ≠ 0 := (Real.rpow_pos_of_pos hmy _).ne'
  rw [integral_mulMeasure_C]
  have hpt : (fun x : ℂ => (‖x‖ ^ 2)⁻¹ *
      ‖u y * ((‖y‖ ^ 2 : ℝ) : ℂ) * F (y * x) * (charExt (complexCharFun 0 k) x * ((‖x‖ ^ 2 : ℝ) : ℂ) ^ (1 - s))‖)
      =ᵐ[volume] fun x : ℂ => (‖u y‖ * ‖y‖ ^ 2 * (‖y‖ ^ 2) ^ s.re) * (‖F (y * x)‖ * (‖y * x‖ ^ 2) ^ (-s.re)) := by
    filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0 : ℂ))] with x hx
    have hx0 : x ≠ 0 := hx
    have hmx : 0 < ‖x‖ ^ 2 := pow_pos (norm_pos_iff.2 hx0) 2
    have hmx' : (‖x‖ ^ 2) ^ s.re ≠ 0 := (Real.rpow_pos_of_pos hmx _).ne'
    rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_charExt_complexCharFun k hx0, one_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos hmx, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hmy,
      Complex.sub_re, Complex.one_re, norm_mul y x, mul_pow, Real.mul_rpow hmy.le hmx.le,
      Real.rpow_neg hmy.le, Real.rpow_neg hmx.le, show (1 : ℝ) - s.re = -s.re + 1 by ring,
      Real.rpow_add_one hmx.ne', Real.rpow_neg hmx.le]
    field_simp
  rw [integral_congr_ae hpt, integral_const_mul,
    integral_comp_mul_left_C_real (fun t : ℂ => ‖F t‖ * (‖t‖ ^ 2) ^ (-s.re)) y]
  field_simp

private theorem integrable_swap_C {u v : ℂ → ℂ} (hu : IsGaussPolyC u) (hv : IsGaussPolyC v) (k : ℤ) {s : ℂ}
    (hs₀ : 0 < s.re) (hs₁ : s.re < 1) :
    Integrable (Function.uncurry fun y x : ℂ =>
        u y * ((modulus y : ℝ) : ℂ) * tateFourier psiComplex volume v (y * x) *
          (charExt (complexCharFun 0 k)⁻¹ x * ((modulus x : ℝ) : ℂ) ^ (1 - s)))
      ((mulMeasure (volume : Measure ℂ)).prod (mulMeasure volume)) := by
  rw [tateFourier_psiComplex, complexCharFun_zero_inv]
  simp_rw [modulus_C_cast]
  obtain ⟨F, hFdef⟩ : ∃ F : ℂ → ℂ, F = FC v := ⟨_, rfl⟩
  rw [← hFdef]
  have hF : IsGaussPolyC F := hFdef ▸ hv.FC
  have hmeas : AEStronglyMeasurable (Function.uncurry fun y x : ℂ =>
      u y * ((‖y‖ ^ 2 : ℝ) : ℂ) * F (y * x) * (charExt (complexCharFun 0 (-k)) x * ((‖x‖ ^ 2 : ℝ) : ℂ) ^ (1 - s)))
      ((mulMeasure (volume : Measure ℂ)).prod (mulMeasure volume)) := by
    refine Measurable.aestronglyMeasurable ?_
    show Measurable fun p : ℂ × ℂ =>
      u p.1 * ((‖p.1‖ ^ 2 : ℝ) : ℂ) * F (p.1 * p.2)
        * (charExt (complexCharFun 0 (-k)) p.2 * ((‖p.2‖ ^ 2 : ℝ) : ℂ) ^ (1 - s))
    exact (((hu.continuous.measurable.comp measurable_fst).mul
        (Complex.measurable_ofReal.comp ((measurable_norm.comp measurable_fst).pow_const 2))).mul
        (hF.continuous.measurable.comp (measurable_fst.mul measurable_snd))).mul
      (((measurable_charExt_complexCharFun (-k)).comp measurable_snd).mul
        ((Complex.measurable_ofReal.comp ((measurable_norm.comp measurable_snd).pow_const 2)).pow_const _))
  haveI := sfinite_mulMeasure_C
  rw [integrable_prod_iff hmeas]
  simp only [Function.uncurry_apply_pair]
  refine ⟨Filter.Eventually.of_forall fun y => ?_, ?_⟩
  · by_cases hy : y = 0
    · subst hy
      simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Complex.ofReal_zero,
        mul_zero, zero_mul]
      exact integrable_zero _ _ _
    · exact integrable_slice_C hF (-k) hs₁ (u y * ((‖y‖ ^ 2 : ℝ) : ℂ)) hy
  · have hval : (fun y : ℂ => ∫ x, ‖u y * ((‖y‖ ^ 2 : ℝ) : ℂ) * F (y * x) *
          (charExt (complexCharFun 0 (-k)) x * ((‖x‖ ^ 2 : ℝ) : ℂ) ^ (1 - s))‖ ∂(mulMeasure (volume : Measure ℂ)))
        = fun y : ℂ => (∫ t : ℂ, ‖F t‖ * (‖t‖ ^ 2) ^ (-s.re)) * (‖u y‖ * (‖y‖ ^ 2) ^ s.re) := by
      funext y
      by_cases hy : y = 0
      · subst hy
        simp [Real.zero_rpow hs₀.ne']
      · rw [integral_norm_slice_C u F (-k) s hy]; ring
    rw [hval, integrable_mulMeasure_iff_C]
    have hint := ((integrable_tateC' hu 0 hs₀).norm).const_mul (∫ t : ℂ, ‖F t‖ * (‖t‖ ^ 2) ^ (-s.re))
    refine hint.congr ?_
    filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0 : ℂ))] with y hy
    have hy0 : y ≠ 0 := hy
    have hmy : 0 < ‖y‖ ^ 2 := pow_pos (norm_pos_iff.2 hy0) 2
    rw [norm_mul, norm_kerC hy0, Real.rpow_sub_one hmy.ne', smul_eq_mul]
    field_simp

private theorem tate_symmetry_C {f g : ℂ → ℂ} (hf : IsGaussPolyC f) (hg : IsGaussPolyC g) (k : ℤ) {s : ℂ}
    (hs₀ : 0 < s.re) (hs₁ : s.re < 1) :
    tateZetaC (FC f) (-k) (1 - s) * tateZetaC g k s = tateZetaC (FC g) (-k) (1 - s) * tateZetaC f k s := by
  have hsym := localZeta_fourier_mul_symm (volume : Measure ℂ) psiComplex f g (complexCharFun 0 k) s
    aemeasurable_modulus_inv_C (integrable_swap_C hg hf k hs₀ hs₁) (integrable_swap_C hf hg k hs₀ hs₁)
    (fun x _ => integrable_kernel_C hf hg x)
  rw [complexCharFun_zero_inv, tateFourier_psiComplex, tateFourier_psiComplex, ← tateZetaC_eq_localZeta,
    ← tateZetaC_eq_localZeta, ← tateZetaC_eq_localZeta, ← tateZetaC_eq_localZeta] at hsym
  exact hsym

end

section
open Complex MeasureTheory LanglandsTunnell.ArchPlace

private theorem tateZetaC_const_mul (c : ℂ) (f : ℂ → ℂ) (k : ℤ) (w : ℂ) :
    tateZetaC (fun z => c * f z) k w = c * tateZetaC f k w := by
  unfold tateZetaC
  simp_rw [mul_assoc]
  exact integral_const_mul c _

private theorem tateZetaC_FC_complexTestFun (k : ℤ) {w : ℂ} (hw : 0 < (1 - w).re) :
    tateZetaC (FC (complexTestFun k)) (-k) (1 - w)
      = cC k * ((Real.pi / 2 : ℂ) * Gammaℂ (1 - w + (k.natAbs : ℂ) / 2)) := by
  rw [FC_complexTestFun', tateZetaC_const_mul, ← Int.natAbs_neg k, tateZetaC_complexTestFun' (-k) hw]

private theorem strip_functional_equation_C' {f : ℂ → ℂ} (hf : IsGaussPolyC f) (k : ℤ) {w : ℂ}
    (hw₀ : 0 < w.re) (hw₁ : w.re < 1) :
    tateZetaC (FC f) (-k) (1 - w) * Gammaℂ (w + (k.natAbs : ℂ) / 2)
      = cC k * Gammaℂ (1 - w + (k.natAbs : ℂ) / 2) * tateZetaC f k w := by
  have h1w : 0 < (1 - w).re := by simp; linarith
  have hsym := tate_symmetry_C hf (isGaussPolyC_complexTestFun' k) k hw₀ hw₁
  rw [tateZetaC_complexTestFun' k hw₀, tateZetaC_FC_complexTestFun k h1w] at hsym
  have hpi : (Real.pi / 2 : ℂ) ≠ 0 := by
    have : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_pos.ne'
    exact div_ne_zero this two_ne_zero
  refine mul_left_cancel₀ hpi ?_
  linear_combination hsym

end

private theorem strip_functional_equation_C {f : ℂ → ℂ} (hf : IsGaussPolyC f) (k : ℤ) {w : ℂ}
    (hw₀ : 0 < w.re) (hw₁ : w.re < 1) :
    tateZetaC (FC f) (-k) (1 - w) * Gammaℂ (w + (k.natAbs : ℂ) / 2)
      = cC k * Gammaℂ (1 - w + (k.natAbs : ℂ) / 2) * tateZetaC f k w :=
  strip_functional_equation_C' hf k hw₀ hw₁

end TateComplex

end

end

section

open Complex

noncomputable section

namespace TateComplex

namespace W3C

private def gexpC (α₁ α₂ : ℝ) (γr γi b₁ b₁' b₂ b₂' : ℂ) (z t : ℂ) : ℂ :=
  (-(2 * Real.pi * α₁ * ‖z‖ ^ 2)
      + 2 * Real.pi * ((b₁ + (γr + γi * I) * starRingEnd ℂ t) * z
        + (b₁' + (starRingEnd ℂ γr + starRingEnd ℂ γi * I) * t) * starRingEnd ℂ z))
    + (-(2 * Real.pi * α₂ * ‖t‖ ^ 2) + 2 * Real.pi * (b₂ * t + b₂' * starRingEnd ℂ t))

private def genC (α₁ α₂ : ℝ) (γr γi b₁ b₁' b₂ b₂' : ℂ) (z t : ℂ) : ℂ := cexp (gexpC α₁ α₂ γr γi b₁ b₁' b₂ b₂' z t)

private structure AdmC (α₁ α₂ : ℝ) (γr γi : ℂ) : Prop where
  h₁ : 0 < α₁
  h₂ : 0 < α₂
  hγ : γr * γi = 0
  hpd : ‖γr‖ ^ 2 < α₁ * α₂

private theorem AdmC.swap {α₁ α₂ : ℝ} {γr γi : ℂ} (h : AdmC α₁ α₂ γr γi) :
    AdmC α₂ α₁ (starRingEnd ℂ γr) (starRingEnd ℂ γi) :=
  ⟨h.h₂, h.h₁, by rw [← map_mul, h.hγ, map_zero], by rw [Complex.norm_conj, mul_comm]; exact h.hpd⟩

private theorem AdmC.rot {α₁ α₂ : ℝ} {γr γi : ℂ} (h : AdmC α₁ α₂ γr γi) {u : ℂ} (hu : ‖u‖ = 1) :
    AdmC α₁ α₂ (u * γr) (u * γi) :=
  ⟨h.h₁, h.h₂, by rw [mul_mul_mul_comm, h.hγ, mul_zero], by rw [norm_mul, hu, one_mul]; exact h.hpd⟩

private inductive ClsC : (ℂ → ℂ → ℂ) → Prop
  | gen {α₁ α₂ : ℝ} {γr γi : ℂ} (b₁ b₁' b₂ b₂' : ℂ) (h : AdmC α₁ α₂ γr γi) :
      ClsC (genC α₁ α₂ γr γi b₁ b₁' b₂ b₂')
  | smul (c : ℂ) {Ψ : ℂ → ℂ → ℂ} (hΨ : ClsC Ψ) : ClsC (fun z t => c * Ψ z t)
  | add {Ψ Φ : ℂ → ℂ → ℂ} (hΨ : ClsC Ψ) (hΦ : ClsC Φ) : ClsC (fun z t => Ψ z t + Φ z t)
  | mulZ {Ψ : ℂ → ℂ → ℂ} (hΨ : ClsC Ψ) : ClsC (fun z t => z * Ψ z t)
  | mulZbar {Ψ : ℂ → ℂ → ℂ} (hΨ : ClsC Ψ) : ClsC (fun z t => starRingEnd ℂ z * Ψ z t)
  | mulT {Ψ : ℂ → ℂ → ℂ} (hΨ : ClsC Ψ) : ClsC (fun z t => t * Ψ z t)
  | mulTbar {Ψ : ℂ → ℂ → ℂ} (hΨ : ClsC Ψ) : ClsC (fun z t => starRingEnd ℂ t * Ψ z t)

namespace ClsC p2m_export "TateComplex.W3C.ClsC" "linear_mul conj_linear_mul linear_pow_mul conj_linear_pow_mul" end ClsC
private theorem ClsC.congr {Ψ Φ : ℂ → ℂ → ℂ} (h : ClsC Ψ) (e : Ψ = Φ) : ClsC Φ := by
  subst e
  exact h

private theorem gexpC_swap (α₁ α₂ : ℝ) (γr γi b₁ b₁' b₂ b₂' : ℂ) (z t : ℂ) :
    gexpC α₁ α₂ γr γi b₁ b₁' b₂ b₂' t z
      = gexpC α₂ α₁ (starRingEnd ℂ γr) (starRingEnd ℂ γi) b₂ b₂' b₁ b₁' z t := by
  simp only [gexpC, Complex.conj_conj]
  ring

private theorem genC_swap (α₁ α₂ : ℝ) (γr γi b₁ b₁' b₂ b₂' : ℂ) :
    (fun z t => genC α₁ α₂ γr γi b₁ b₁' b₂ b₂' t z)
      = genC α₂ α₁ (starRingEnd ℂ γr) (starRingEnd ℂ γi) b₂ b₂' b₁ b₁' := by
  funext z t
  simp only [genC]
  rw [gexpC_swap]

private theorem ClsC.swap {Ψ : ℂ → ℂ → ℂ} (h : ClsC Ψ) : ClsC (fun z t => Ψ t z) := by
  induction h with
  | @gen α₁ α₂ γr γi b₁ b₁' b₂ b₂' hadm =>
    exact (ClsC.gen b₂ b₂' b₁ b₁' hadm.swap).congr (genC_swap α₁ α₂ γr γi b₁ b₁' b₂ b₂').symm
  | smul c _ ih => exact ih.smul c
  | add _ _ ih₁ ih₂ => exact ih₁.add ih₂
  | mulZ _ ih => exact ih.mulT
  | mulZbar _ ih => exact ih.mulTbar
  | mulT _ ih => exact ih.mulZ
  | mulTbar _ ih => exact ih.mulZbar

private theorem norm_unit_mul {u : ℂ} (hu : ‖u‖ = 1) (z : ℂ) : ‖u * z‖ = ‖z‖ := by
  rw [norm_mul, hu, one_mul]

private theorem conj_unit_mul_self {u : ℂ} (hu : ‖u‖ = 1) : starRingEnd ℂ u * u = 1 := by
  rw [Complex.conj_mul', hu]
  simp

private theorem gexpC_rot (α₁ α₂ : ℝ) (γr γi b₁ b₁' b₂ b₂' : ℂ) {u : ℂ} (hu : ‖u‖ = 1) (z t : ℂ) :
    gexpC α₁ α₂ γr γi b₁ b₁' b₂ b₂' (u * z) t
      = gexpC α₁ α₂ (u * γr) (u * γi) (u * b₁) (starRingEnd ℂ u * b₁') b₂ b₂' z t := by
  simp only [gexpC, norm_unit_mul hu, map_mul]
  ring

private theorem genC_rot (α₁ α₂ : ℝ) (γr γi b₁ b₁' b₂ b₂' : ℂ) {u : ℂ} (hu : ‖u‖ = 1) :
    (fun z t => genC α₁ α₂ γr γi b₁ b₁' b₂ b₂' (u * z) t)
      = genC α₁ α₂ (u * γr) (u * γi) (u * b₁) (starRingEnd ℂ u * b₁') b₂ b₂' := by
  funext z t
  simp only [genC]
  rw [gexpC_rot _ _ _ _ _ _ _ _ hu]

private theorem ClsC.rot {Ψ : ℂ → ℂ → ℂ} (h : ClsC Ψ) {u : ℂ} (hu : ‖u‖ = 1) : ClsC (fun z t => Ψ (u * z) t) := by
  induction h with
  | @gen α₁ α₂ γr γi b₁ b₁' b₂ b₂' hadm =>
    exact (ClsC.gen (u * b₁) (starRingEnd ℂ u * b₁') b₂ b₂' (hadm.rot hu)).congr
      (genC_rot α₁ α₂ γr γi b₁ b₁' b₂ b₂' hu).symm
  | smul c _ ih => exact ih.smul c
  | add _ _ ih₁ ih₂ => exact ih₁.add ih₂
  | mulZ _ ih => exact (ih.mulZ.smul u).congr (by funext z t; ring)
  | mulZbar _ ih => exact (ih.mulZbar.smul (starRingEnd ℂ u)).congr (by funext z t; simp only [map_mul]; ring)
  | mulT _ ih => exact ih.mulT
  | mulTbar _ ih => exact ih.mulTbar

private theorem ClsC.reflZ {Ψ : ℂ → ℂ → ℂ} (h : ClsC Ψ) : ClsC (fun z t => Ψ (-z) t) :=
  (h.rot (u := -1) (by simp)).congr (by funext z t; simp)

private theorem continuous_genC (α₁ α₂ : ℝ) (γr γi b₁ b₁' b₂ b₂' : ℂ) :
    Continuous (fun p : ℂ × ℂ => genC α₁ α₂ γr γi b₁ b₁' b₂ b₂' p.1 p.2) := by
  unfold genC gexpC
  fun_prop

private theorem ClsC.continuous {Ψ : ℂ → ℂ → ℂ} (h : ClsC Ψ) : Continuous (fun p : ℂ × ℂ => Ψ p.1 p.2) := by
  induction h with
  | gen b₁ b₁' b₂ b₂' _ => exact continuous_genC _ _ _ _ b₁ b₁' b₂ b₂'
  | smul c _ ih => exact continuous_const.mul ih
  | add _ _ ih₁ ih₂ => exact ih₁.add ih₂
  | mulZ _ ih => exact continuous_fst.mul ih
  | mulZbar _ ih => exact (Complex.continuous_conj.comp continuous_fst).mul ih
  | mulT _ ih => exact continuous_snd.mul ih
  | mulTbar _ ih => exact (Complex.continuous_conj.comp continuous_snd).mul ih

private theorem gexpC_re (α₁ α₂ : ℝ) (γr γi b₁ b₁' b₂ b₂' : ℂ) (z t : ℂ) :
    (gexpC α₁ α₂ γr γi b₁ b₁' b₂ b₂' z t).re
      = -(2 * Real.pi) * (α₁ * ‖z‖ ^ 2 + α₂ * ‖t‖ ^ 2 - 2 * (γr * z * starRingEnd ℂ t).re)
        + 2 * Real.pi * (b₁ * z + b₁' * starRingEnd ℂ z + b₂ * t + b₂' * starRingEnd ℂ t).re := by
  simp only [gexpC, Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.add_im, Complex.re_ofNat, Complex.im_ofNat,
    Complex.conj_re, Complex.conj_im]
  simp only [← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_im]
  ring

private theorem AdmC.exists_lower {α₁ α₂ : ℝ} {γr γi : ℂ} (h : AdmC α₁ α₂ γr γi) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ z t : ℂ,
      lam * (‖z‖ ^ 2 + ‖t‖ ^ 2) ≤ α₁ * ‖z‖ ^ 2 + α₂ * ‖t‖ ^ 2 - 2 * (γr * z * starRingEnd ℂ t).re := by
  obtain ⟨lam, hlam, hQ⟩ := TateReal.W3.exists_pd_lower (γr := ‖γr‖) h.h₁ h.h₂ h.hpd
  refine ⟨lam, hlam, fun z t => ?_⟩
  have hre : (γr * z * starRingEnd ℂ t).re ≤ ‖γr‖ * ‖z‖ * ‖t‖ := by
    calc (γr * z * starRingEnd ℂ t).re ≤ ‖γr * z * starRingEnd ℂ t‖ :=
          (le_abs_self _).trans (Complex.abs_re_le_norm _)
      _ = ‖γr‖ * ‖z‖ * ‖t‖ := by rw [norm_mul, norm_mul, Complex.norm_conj]
  have hq := hQ ‖z‖ ‖t‖
  linarith

private theorem norm_genC_le {α₁ α₂ : ℝ} {γr γi : ℂ} (b₁ b₁' b₂ b₂' : ℂ) (h : AdmC α₁ α₂ γr γi) :
    ∃ (K δ : ℝ), 0 < δ ∧ ∀ z t : ℂ,
      ‖genC α₁ α₂ γr γi b₁ b₁' b₂ b₂' z t‖ ≤ Real.exp K * Real.exp (-δ * (‖z‖ ^ 2 + ‖t‖ ^ 2)) := by
  obtain ⟨lam, hlam, hQ⟩ := h.exists_lower
  refine ⟨2 * Real.pi * ((‖b₁‖ + ‖b₁'‖) ^ 2 / lam + (‖b₂‖ + ‖b₂'‖) ^ 2 / lam), Real.pi * lam, by positivity,
    fun z t => ?_⟩
  rw [genC, Complex.norm_exp, ← Real.exp_add, gexpC_re]
  apply Real.exp_le_exp.mpr
  have hlin : (b₁ * z + b₁' * starRingEnd ℂ z + b₂ * t + b₂' * starRingEnd ℂ t).re
      ≤ (‖b₁‖ + ‖b₁'‖) * ‖z‖ + (‖b₂‖ + ‖b₂'‖) * ‖t‖ := by
    have h4 : ‖b₁ * z + b₁' * starRingEnd ℂ z + b₂ * t + b₂' * starRingEnd ℂ t‖
        ≤ ‖b₁ * z‖ + ‖b₁' * starRingEnd ℂ z‖ + ‖b₂ * t‖ + ‖b₂' * starRingEnd ℂ t‖ :=
      (norm_add_le _ _).trans
        (add_le_add ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
    simp only [norm_mul, Complex.norm_conj] at h4
    have h5 := (le_abs_self _).trans
      (Complex.abs_re_le_norm (b₁ * z + b₁' * starRingEnd ℂ z + b₂ * t + b₂' * starRingEnd ℂ t))
    linarith
  have amgm : ∀ b y : ℝ, b * y ≤ lam / 4 * y ^ 2 + b ^ 2 / lam := fun b y => by
    rw [← sub_nonneg]
    have e : lam / 4 * y ^ 2 + b ^ 2 / lam - b * y = (lam * y - 2 * b) ^ 2 / (4 * lam) := by
      field_simp
      ring
    rw [e]
    positivity
  have hx := amgm (‖b₁‖ + ‖b₁'‖) ‖z‖
  have ht := amgm (‖b₂‖ + ‖b₂'‖) ‖t‖
  have hQ' := hQ z t
  have hpi := Real.pi_pos
  have hS : 0 ≤ ‖z‖ ^ 2 + ‖t‖ ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hx (by positivity : (0:ℝ) ≤ 2 * Real.pi),
    mul_le_mul_of_nonneg_left ht (by positivity : (0:ℝ) ≤ 2 * Real.pi),
    mul_le_mul_of_nonneg_left hQ' hpi.le, mul_le_mul_of_nonneg_left hlin (by positivity : (0:ℝ) ≤ 2 * Real.pi),
    mul_nonneg hpi.le (mul_nonneg hlam.le hS)]

private theorem ClsC.bound {Ψ : ℂ → ℂ → ℂ} (h : ClsC Ψ) :
    ∃ (C : ℝ) (N : ℕ) (δ : ℝ), 0 ≤ C ∧ 0 < δ ∧
      ∀ z t : ℂ, ‖Ψ z t‖ ≤ C * (1 + ‖z‖ + ‖t‖) ^ N * Real.exp (-δ * (‖z‖ ^ 2 + ‖t‖ ^ 2)) := by
  induction h with
  | gen b₁ b₁' b₂ b₂' hadm =>
    obtain ⟨K, δ, hδ, hb⟩ := norm_genC_le b₁ b₁' b₂ b₂' hadm
    exact ⟨Real.exp K, 0, δ, (Real.exp_pos _).le, hδ, fun z t => by simpa using hb z t⟩
  | smul c _ ih =>
    obtain ⟨C, N, δ, hC, hδ, hb⟩ := ih
    refine ⟨‖c‖ * C, N, δ, by positivity, hδ, fun z t => ?_⟩
    rw [norm_mul]
    calc ‖c‖ * ‖_‖ ≤ ‖c‖ * (C * (1 + ‖z‖ + ‖t‖) ^ N * Real.exp (-δ * (‖z‖ ^ 2 + ‖t‖ ^ 2))) :=
          mul_le_mul_of_nonneg_left (hb z t) (norm_nonneg _)
      _ = ‖c‖ * C * (1 + ‖z‖ + ‖t‖) ^ N * Real.exp (-δ * (‖z‖ ^ 2 + ‖t‖ ^ 2)) := by ring
  | add _ _ ih₁ ih₂ =>
    obtain ⟨C₁, N₁, δ₁, hC₁, hδ₁, hb₁⟩ := ih₁
    obtain ⟨C₂, N₂, δ₂, hC₂, hδ₂, hb₂⟩ := ih₂
    refine ⟨C₁ + C₂, max N₁ N₂, min δ₁ δ₂, by positivity, lt_min hδ₁ hδ₂, fun z t => ?_⟩
    have hB : 1 ≤ 1 + ‖z‖ + ‖t‖ := by linarith [norm_nonneg z, norm_nonneg t]
    have hr : 0 ≤ ‖z‖ ^ 2 + ‖t‖ ^ 2 := by positivity
    have hp₁ : (1 + ‖z‖ + ‖t‖) ^ N₁ ≤ (1 + ‖z‖ + ‖t‖) ^ max N₁ N₂ :=
      pow_le_pow_right₀ hB (le_max_left _ _)
    have hp₂ : (1 + ‖z‖ + ‖t‖) ^ N₂ ≤ (1 + ‖z‖ + ‖t‖) ^ max N₁ N₂ :=
      pow_le_pow_right₀ hB (le_max_right _ _)
    have he₁ : Real.exp (-δ₁ * (‖z‖ ^ 2 + ‖t‖ ^ 2)) ≤ Real.exp (-min δ₁ δ₂ * (‖z‖ ^ 2 + ‖t‖ ^ 2)) :=
      Real.exp_le_exp.mpr (by nlinarith [min_le_left δ₁ δ₂])
    have he₂ : Real.exp (-δ₂ * (‖z‖ ^ 2 + ‖t‖ ^ 2)) ≤ Real.exp (-min δ₁ δ₂ * (‖z‖ ^ 2 + ‖t‖ ^ 2)) :=
      Real.exp_le_exp.mpr (by nlinarith [min_le_right δ₁ δ₂])
    calc ‖_ + _‖ ≤ ‖_‖ + ‖_‖ := norm_add_le _ _
      _ ≤ C₁ * (1 + ‖z‖ + ‖t‖) ^ N₁ * Real.exp (-δ₁ * (‖z‖ ^ 2 + ‖t‖ ^ 2))
          + C₂ * (1 + ‖z‖ + ‖t‖) ^ N₂ * Real.exp (-δ₂ * (‖z‖ ^ 2 + ‖t‖ ^ 2)) := add_le_add (hb₁ z t) (hb₂ z t)
      _ ≤ C₁ * (1 + ‖z‖ + ‖t‖) ^ max N₁ N₂ * Real.exp (-min δ₁ δ₂ * (‖z‖ ^ 2 + ‖t‖ ^ 2))
          + C₂ * (1 + ‖z‖ + ‖t‖) ^ max N₁ N₂ * Real.exp (-min δ₁ δ₂ * (‖z‖ ^ 2 + ‖t‖ ^ 2)) := by gcongr
      _ = (C₁ + C₂) * (1 + ‖z‖ + ‖t‖) ^ max N₁ N₂ * Real.exp (-min δ₁ δ₂ * (‖z‖ ^ 2 + ‖t‖ ^ 2)) := by ring
  | mulZ _ ih =>
    obtain ⟨C, N, δ, hC, hδ, hb⟩ := ih
    refine ⟨C, N + 1, δ, hC, hδ, fun z t => ?_⟩
    rw [norm_mul, pow_succ]
    have hzB : ‖z‖ ≤ 1 + ‖z‖ + ‖t‖ := by linarith [norm_nonneg t]
    calc ‖z‖ * ‖_‖ ≤ ‖z‖ * (C * (1 + ‖z‖ + ‖t‖) ^ N * Real.exp (-δ * (‖z‖ ^ 2 + ‖t‖ ^ 2))) :=
          mul_le_mul_of_nonneg_left (hb z t) (norm_nonneg _)
      _ ≤ (1 + ‖z‖ + ‖t‖) * (C * (1 + ‖z‖ + ‖t‖) ^ N * Real.exp (-δ * (‖z‖ ^ 2 + ‖t‖ ^ 2))) := by gcongr
      _ = C * ((1 + ‖z‖ + ‖t‖) ^ N * (1 + ‖z‖ + ‖t‖)) * Real.exp (-δ * (‖z‖ ^ 2 + ‖t‖ ^ 2)) := by ring
  | mulZbar _ ih =>
    obtain ⟨C, N, δ, hC, hδ, hb⟩ := ih
    refine ⟨C, N + 1, δ, hC, hδ, fun z t => ?_⟩
    rw [norm_mul, Complex.norm_conj, pow_succ]
    have hzB : ‖z‖ ≤ 1 + ‖z‖ + ‖t‖ := by linarith [norm_nonneg t]
    calc ‖z‖ * ‖_‖ ≤ ‖z‖ * (C * (1 + ‖z‖ + ‖t‖) ^ N * Real.exp (-δ * (‖z‖ ^ 2 + ‖t‖ ^ 2))) :=
          mul_le_mul_of_nonneg_left (hb z t) (norm_nonneg _)
      _ ≤ (1 + ‖z‖ + ‖t‖) * (C * (1 + ‖z‖ + ‖t‖) ^ N * Real.exp (-δ * (‖z‖ ^ 2 + ‖t‖ ^ 2))) := by gcongr
      _ = C * ((1 + ‖z‖ + ‖t‖) ^ N * (1 + ‖z‖ + ‖t‖)) * Real.exp (-δ * (‖z‖ ^ 2 + ‖t‖ ^ 2)) := by ring
  | mulT _ ih =>
    obtain ⟨C, N, δ, hC, hδ, hb⟩ := ih
    refine ⟨C, N + 1, δ, hC, hδ, fun z t => ?_⟩
    rw [norm_mul, pow_succ]
    have htB : ‖t‖ ≤ 1 + ‖z‖ + ‖t‖ := by linarith [norm_nonneg z]
    calc ‖t‖ * ‖_‖ ≤ ‖t‖ * (C * (1 + ‖z‖ + ‖t‖) ^ N * Real.exp (-δ * (‖z‖ ^ 2 + ‖t‖ ^ 2))) :=
          mul_le_mul_of_nonneg_left (hb z t) (norm_nonneg _)
      _ ≤ (1 + ‖z‖ + ‖t‖) * (C * (1 + ‖z‖ + ‖t‖) ^ N * Real.exp (-δ * (‖z‖ ^ 2 + ‖t‖ ^ 2))) := by gcongr
      _ = C * ((1 + ‖z‖ + ‖t‖) ^ N * (1 + ‖z‖ + ‖t‖)) * Real.exp (-δ * (‖z‖ ^ 2 + ‖t‖ ^ 2)) := by ring
  | mulTbar _ ih =>
    obtain ⟨C, N, δ, hC, hδ, hb⟩ := ih
    refine ⟨C, N + 1, δ, hC, hδ, fun z t => ?_⟩
    rw [norm_mul, Complex.norm_conj, pow_succ]
    have htB : ‖t‖ ≤ 1 + ‖z‖ + ‖t‖ := by linarith [norm_nonneg z]
    calc ‖t‖ * ‖_‖ ≤ ‖t‖ * (C * (1 + ‖z‖ + ‖t‖) ^ N * Real.exp (-δ * (‖z‖ ^ 2 + ‖t‖ ^ 2))) :=
          mul_le_mul_of_nonneg_left (hb z t) (norm_nonneg _)
      _ ≤ (1 + ‖z‖ + ‖t‖) * (C * (1 + ‖z‖ + ‖t‖) ^ N * Real.exp (-δ * (‖z‖ ^ 2 + ‖t‖ ^ 2))) := by gcongr
      _ = C * ((1 + ‖z‖ + ‖t‖) ^ N * (1 + ‖z‖ + ‖t‖)) * Real.exp (-δ * (‖z‖ ^ 2 + ‖t‖ ^ 2)) := by ring

end W3C

end TateComplex

end

end

section

open Complex MeasureTheory LanglandsTunnell.TateLocal LanglandsTunnell.ArchPlace
open scoped FourierTransform

noncomputable section

namespace TateComplex

namespace W3C

private def _root_.TateComplex.W3C.F₁C (Ψ : ℂ → ℂ → ℂ) (ξ t : ℂ) : ℂ := FC (fun z => Ψ z t) (starRingEnd ℂ ξ)

p2m_export "TateComplex.W3C" "F₁C"
private def _root_.TateComplex.W3C.F₂C (Ψ : ℂ → ℂ → ℂ) (z τ : ℂ) : ℂ := FC (fun t => Ψ z t) (starRingEnd ℂ τ)

p2m_export "TateComplex.W3C" "F₂C"
private theorem F₂C_eq_swap_F₁C_swap (Ψ : ℂ → ℂ → ℂ) : F₂C Ψ = fun z τ => F₁C (fun a b => Ψ b a) τ z := rfl

private theorem FC_gaussC {α : ℝ} (hα : 0 < α) (B₁ B₂ w : ℂ) :
    FC (fun z => cexp (-(2 * Real.pi * α * ‖z‖ ^ 2) + 2 * Real.pi * (B₁ * z + B₂ * starRingEnd ℂ z))) w
      = 1 / (2 * α) * cexp (2 * Real.pi * ((B₁ - I * w) * (B₂ - I * starRingEnd ℂ w)) / α) := by
  obtain ⟨a, b, hw⟩ : ∃ a b : ℝ, w = a + b * I := ⟨w.re, w.im, (Complex.re_add_im w).symm⟩
  subst hw
  have h2α : (0 : ℝ) < 2 * α := by positivity
  have hb2 : 0 < (2 * (α : ℂ)).re := by
    simp only [Complex.mul_re, Complex.re_ofNat, Complex.ofReal_re, Complex.im_ofNat, Complex.ofReal_im, mul_zero,
      sub_zero]
    exact h2α
  have h2α0 : (2 * (α : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr hα.ne')

  have hF : ∀ pt : ℝ × ℝ,
      cexp (-(2 * Real.pi * α * ‖(pt.1 + pt.2 * I : ℂ)‖ ^ 2)
            + 2 * Real.pi * (B₁ * (pt.1 + pt.2 * I) + B₂ * starRingEnd ℂ (pt.1 + pt.2 * I)))
          * psiComplex ((pt.1 + pt.2 * I) * (a + b * I))
        = (cexp (((-2 * Real.pi * pt.1 * (2 * a) : ℝ) : ℂ) * I)
            * cexp (-Real.pi * (2 * α) * (pt.1 : ℂ) ^ 2 + 2 * Real.pi * (B₁ + B₂) * pt.1))
          * (cexp (((-2 * Real.pi * pt.2 * (-2 * b) : ℝ) : ℂ) * I)
            * cexp (-Real.pi * (2 * α) * (pt.2 : ℂ) ^ 2 + 2 * Real.pi * (I * (B₁ - B₂)) * pt.2)) := by
    intro pt
    rw [psiComplex_coords, cexp_split]
    ring

  have hx : ∫ x : ℝ, cexp (((-2 * Real.pi * x * (2 * a) : ℝ) : ℂ) * I)
        * cexp (-Real.pi * (2 * α) * (x : ℂ) ^ 2 + 2 * Real.pi * (B₁ + B₂) * x)
      = 𝓕 (fun x : ℝ => cexp (-Real.pi * (2 * α) * (x : ℂ) ^ 2 + 2 * Real.pi * (B₁ + B₂) * x)) (2 * a) :=
    integral_kernel_mul_eq_fourier _ _
  have ht : ∫ t : ℝ, cexp (((-2 * Real.pi * t * (-2 * b) : ℝ) : ℂ) * I)
        * cexp (-Real.pi * (2 * α) * (t : ℂ) ^ 2 + 2 * Real.pi * (I * (B₁ - B₂)) * t)
      = 𝓕 (fun t : ℝ => cexp (-Real.pi * (2 * α) * (t : ℂ) ^ 2 + 2 * Real.pi * (I * (B₁ - B₂)) * t)) (-2 * b) :=
    integral_kernel_mul_eq_fourier _ _
  have hprod := MeasureTheory.integral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    (fun x : ℝ => cexp (((-2 * Real.pi * x * (2 * a) : ℝ) : ℂ) * I)
      * cexp (-Real.pi * (2 * α) * (x : ℂ) ^ 2 + 2 * Real.pi * (B₁ + B₂) * x))
    (fun t : ℝ => cexp (((-2 * Real.pi * t * (-2 * b) : ℝ) : ℂ) * I)
      * cexp (-Real.pi * (2 * α) * (t : ℂ) ^ 2 + 2 * Real.pi * (I * (B₁ - B₂)) * t))
  beta_reduce at hprod
  have hsq : (2 * (α : ℂ)) ^ (1 / 2 : ℂ) * (2 * (α : ℂ)) ^ (1 / 2 : ℂ) = 2 * α := by
    rw [← Complex.cpow_add _ _ h2α0]
    norm_num
  unfold FC tateFourier
  rw [integral_complex_eq_prod]
  beta_reduce
  refine (integral_congr_ae (Filter.Eventually.of_forall hF)).trans ?_
  rw [Measure.volume_eq_prod, hprod, hx, ht]
  simp only [fourier_gaussian_pi' hb2]
  rw [show ∀ s e₁ e₂ : ℂ, 1 / s * cexp e₁ * (1 / s * cexp e₂) = 1 / (s * s) * cexp (e₁ + e₂) from
    fun s e₁ e₂ => by rw [Complex.exp_add]; ring, hsq]
  congr 2
  simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  linear_combination (-(Real.pi : ℂ) / (2 * α) * (4 * (a : ℂ) ^ 2 - 4 * (b : ℂ) ^ 2 * (I ^ 2 - 1)
    + (B₁ + B₂) ^ 2 + (I ^ 2 - 1) * (B₁ - B₂) ^ 2)) * Complex.I_sq

private theorem FC_const_mul (c : ℂ) (f : ℂ → ℂ) : FC (fun z => c * f z) = fun w => c * FC f w := by
  funext w
  unfold FC tateFourier
  beta_reduce
  rw [← integral_const_mul]
  congr 1
  funext z
  ring

private theorem genC_slice (α₁ α₂ : ℝ) (γr γi b₁ b₁' b₂ b₂' : ℂ) (t : ℂ) :
    (fun z => genC α₁ α₂ γr γi b₁ b₁' b₂ b₂' z t)
      = fun z => cexp (-(2 * Real.pi * α₂ * ‖t‖ ^ 2) + 2 * Real.pi * (b₂ * t + b₂' * starRingEnd ℂ t))
          * cexp (-(2 * Real.pi * α₁ * ‖z‖ ^ 2)
              + 2 * Real.pi * ((b₁ + (γr + γi * I) * starRingEnd ℂ t) * z
                + (b₁' + (starRingEnd ℂ γr + starRingEnd ℂ γi * I) * t) * starRingEnd ℂ z)) := by
  funext z
  rw [genC, gexpC, Complex.exp_add, mul_comm]

private theorem AdmC.transformed {α₁ α₂ : ℝ} {γr γi : ℂ} (h : AdmC α₁ α₂ γr γi) :
    AdmC (1 / α₁) (α₂ - (‖γr‖ ^ 2 - ‖γi‖ ^ 2) / α₁) (γi / α₁) (-γr / α₁) := by
  have h₁ := h.h₁
  have hpd := h.hpd
  refine ⟨by positivity, ?_, ?_, ?_⟩
  · rw [sub_pos, div_lt_iff₀ h₁]
    nlinarith [sq_nonneg ‖γi‖]
  · rw [div_mul_div_comm, mul_neg, mul_comm γi γr, h.hγ, neg_zero, zero_div]
  · have key : 1 / α₁ * (α₂ - (‖γr‖ ^ 2 - ‖γi‖ ^ 2) / α₁) - ‖γi / α₁‖ ^ 2 = (α₁ * α₂ - ‖γr‖ ^ 2) / α₁ ^ 2 := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h₁]
      field_simp
      ring
    rw [← sub_pos, key]
    exact div_pos (by linarith) (by positivity)

private theorem F₁C_genC {α₁ α₂ : ℝ} {γr γi : ℂ} (b₁ b₁' b₂ b₂' : ℂ) (h : AdmC α₁ α₂ γr γi) :
    F₁C (genC α₁ α₂ γr γi b₁ b₁' b₂ b₂')
      = fun ξ t => (1 / (2 * α₁) * cexp (2 * Real.pi * b₁ * b₁' / α₁))
          * genC (1 / α₁) (α₂ - (‖γr‖ ^ 2 - ‖γi‖ ^ 2) / α₁) (γi / α₁) (-γr / α₁) (-I * b₁ / α₁)
              (-I * b₁' / α₁) (b₂ + b₁ * (starRingEnd ℂ γr + starRingEnd ℂ γi * I) / α₁)
              (b₂' + b₁' * (γr + γi * I) / α₁) ξ t := by
  funext ξ t
  have hr : γr * starRingEnd ℂ γr = ((‖γr‖ : ℝ) : ℂ) ^ 2 := Complex.mul_conj' γr
  have hi : γi * starRingEnd ℂ γi = ((‖γi‖ : ℝ) : ℂ) ^ 2 := Complex.mul_conj' γi
  have hξ : ξ * starRingEnd ℂ ξ = ((‖ξ‖ : ℝ) : ℂ) ^ 2 := Complex.mul_conj' ξ
  have ht : t * starRingEnd ℂ t = ((‖t‖ : ℝ) : ℂ) ^ 2 := Complex.mul_conj' t
  have h6 : γr * starRingEnd ℂ γi = 0 := by
    rcases mul_eq_zero.mp h.hγ with h0 | h0
    · rw [h0, zero_mul]
    · rw [h0, map_zero, mul_zero]
  have h7 : γi * starRingEnd ℂ γr = 0 := by
    rcases mul_eq_zero.mp h.hγ with h0 | h0
    · rw [h0, map_zero, mul_zero]
    · rw [h0, zero_mul]
  simp only [F₁C]
  rw [genC_slice, FC_const_mul]
  beta_reduce
  rw [FC_gaussC h.h₁, Complex.conj_conj, genC,
    show ∀ p q r : ℂ, cexp p * (q * cexp r) = q * cexp (p + r) from fun p q r => by rw [Complex.exp_add]; ring,
    show ∀ q k e : ℂ, q * cexp k * cexp e = q * cexp (k + e) from fun q k e => by rw [Complex.exp_add]; ring]
  congr 2
  rw [gexpC]
  simp only [map_div₀, map_neg, Complex.conj_ofReal]
  push_cast
  linear_combination (1 / (α₁ : ℂ)) * (2 * Real.pi * (starRingEnd ℂ γi * t - ξ)
      * (starRingEnd ℂ t * γi - starRingEnd ℂ ξ)) * Complex.I_sq
    + (1 / (α₁ : ℂ)) * (-2 * (Real.pi : ℂ)) * hξ
    + (1 / (α₁ : ℂ)) * (2 * Real.pi * (I * starRingEnd ℂ γi * γr + I * starRingEnd ℂ γr * γi
      - starRingEnd ℂ γi * γi + starRingEnd ℂ γr * γr)) * ht
    + (1 / (α₁ : ℂ)) * (2 * ((‖t‖ : ℝ) : ℂ) ^ 2 * Real.pi) * hr
    + (1 / (α₁ : ℂ)) * (-2 * ((‖t‖ : ℝ) : ℂ) ^ 2 * Real.pi) * hi
    + (1 / (α₁ : ℂ)) * (2 * I * ((‖t‖ : ℝ) : ℂ) ^ 2 * Real.pi) * h6
    + (1 / (α₁ : ℂ)) * (2 * I * ((‖t‖ : ℝ) : ℂ) ^ 2 * Real.pi) * h7

end W3C

end TateComplex

end

end

section

open Complex MeasureTheory LanglandsTunnell.TateLocal LanglandsTunnell.ArchPlace
open scoped FourierTransform

noncomputable section

namespace TateComplex

namespace W3C

private inductive InSpanC : (ℂ → ℂ) → Prop
  | mem {f : ℂ → ℂ} (hf : IsGaussPolyC f) : InSpanC f
  | smul (c : ℂ) {f : ℂ → ℂ} (hf : InSpanC f) : InSpanC (fun w => c * f w)
  | add {f g : ℂ → ℂ} (hf : InSpanC f) (hg : InSpanC g) : InSpanC (fun w => f w + g w)

private theorem InSpanC.congr {f g : ℂ → ℂ} (h : InSpanC f) (e : f = g) : InSpanC g := by
  subst e
  exact h

private theorem gaussPolyC_X_mul (p : MvPolynomial (Fin 2) ℂ) (α : ℝ) (β₁ β₂ : ℂ) :
    (fun z : ℂ => z * gaussPolyC p α β₁ β₂ z) = gaussPolyC (MvPolynomial.X 0 * p) α β₁ β₂ := by
  funext z
  simp only [gaussPolyC, MvPolynomial.eval_mul, MvPolynomial.eval_X, Matrix.cons_val_zero]
  ring

private theorem gaussPolyC_Xbar_mul (p : MvPolynomial (Fin 2) ℂ) (α : ℝ) (β₁ β₂ : ℂ) :
    (fun z : ℂ => starRingEnd ℂ z * gaussPolyC p α β₁ β₂ z) = gaussPolyC (MvPolynomial.X 1 * p) α β₁ β₂ := by
  funext z
  simp only [gaussPolyC, MvPolynomial.eval_mul, MvPolynomial.eval_X, Matrix.cons_val_one, Matrix.cons_val_zero]
  ring

private theorem InSpanC.mulZ {f : ℂ → ℂ} (h : InSpanC f) : InSpanC (fun w => w * f w) := by
  induction h with
  | mem hf =>
    obtain ⟨p, α, β₁, β₂, hα, rfl⟩ := hf
    exact (InSpanC.mem ⟨MvPolynomial.X 0 * p, α, β₁, β₂, hα, rfl⟩).congr (gaussPolyC_X_mul p α β₁ β₂).symm
  | smul c _ ih =>
    refine (ih.smul c).congr ?_
    funext w
    ring
  | add _ _ ih₁ ih₂ =>
    refine (ih₁.add ih₂).congr ?_
    funext w
    ring

private theorem InSpanC.mulZbar {f : ℂ → ℂ} (h : InSpanC f) : InSpanC (fun w => starRingEnd ℂ w * f w) := by
  induction h with
  | mem hf =>
    obtain ⟨p, α, β₁, β₂, hα, rfl⟩ := hf
    exact (InSpanC.mem ⟨MvPolynomial.X 1 * p, α, β₁, β₂, hα, rfl⟩).congr (gaussPolyC_Xbar_mul p α β₁ β₂).symm
  | smul c _ ih =>
    refine (ih.smul c).congr ?_
    funext w
    ring
  | add _ _ ih₁ ih₂ =>
    refine (ih₁.add ih₂).congr ?_
    funext w
    ring

private theorem kerC_zero_one_fun : kerC 0 1 = fun _ => (1 : ℂ) := by
  funext z
  simp [kerC]

private theorem integrable_of_isGaussPolyC {f : ℂ → ℂ} (hf : IsGaussPolyC f) : Integrable f := by
  simpa [kerC_zero_one_fun] using integrable_tateC hf 0 (w := 1) (by simp)

private theorem InSpanC.integrable {f : ℂ → ℂ} (h : InSpanC f) : Integrable f := by
  induction h with
  | mem hf => exact integrable_of_isGaussPolyC hf
  | smul c _ ih => exact ih.const_mul c
  | add _ _ ih₁ ih₂ => exact ih₁.add ih₂

private theorem InSpanC.integrable_norm_mul {f : ℂ → ℂ} (h : InSpanC f) : Integrable fun w : ℂ => ‖w‖ * ‖f w‖ := by
  simpa [norm_mul] using h.mulZ.integrable.norm

private theorem isGaussPolyC_genC_slice {α₁ α₂ : ℝ} {γr γi : ℂ} (b₁ b₁' b₂ b₂' : ℂ) (h : AdmC α₁ α₂ γr γi) (t : ℂ) :
    IsGaussPolyC (fun z => genC α₁ α₂ γr γi b₁ b₁' b₂ b₂' z t) := by
  refine ⟨MvPolynomial.C (cexp (-(2 * Real.pi * α₂ * ‖t‖ ^ 2) + 2 * Real.pi * (b₂ * t + b₂' * starRingEnd ℂ t))),
    α₁, b₁ + (γr + γi * I) * starRingEnd ℂ t, b₁' + (starRingEnd ℂ γr + starRingEnd ℂ γi * I) * t, h.h₁, ?_⟩
  rw [genC_slice]
  funext z
  simp only [gaussPolyC, MvPolynomial.eval_C]

private theorem ClsC.sliceZ {Ψ : ℂ → ℂ → ℂ} (h : ClsC Ψ) (t : ℂ) : InSpanC (fun z => Ψ z t) := by
  induction h with
  | gen b₁ b₁' b₂ b₂' hadm => exact InSpanC.mem (isGaussPolyC_genC_slice b₁ b₁' b₂ b₂' hadm t)
  | smul c _ ih => exact ih.smul c
  | add _ _ ih₁ ih₂ => exact ih₁.add ih₂
  | mulZ _ ih => exact ih.mulZ
  | mulZbar _ ih => exact ih.mulZbar
  | mulT _ ih => exact ih.smul t
  | mulTbar _ ih => exact ih.smul _

private theorem ClsC.integrable_sliceZ {Ψ : ℂ → ℂ → ℂ} (h : ClsC Ψ) (t : ℂ) : Integrable (fun z => Ψ z t) :=
  (h.sliceZ t).integrable

private theorem ClsC.integrable_norm_mul_sliceZ {Ψ : ℂ → ℂ → ℂ} (h : ClsC Ψ) (t : ℂ) :
    Integrable fun z : ℂ => ‖z‖ * ‖Ψ z t‖ :=
  (h.sliceZ t).integrable_norm_mul

private def lineD (h : ℂ) (Ψ : ℂ → ℂ → ℂ) (ξ t : ℂ) : ℂ := deriv (fun s : ℝ => Ψ (ξ + (s : ℂ) * h) t) 0

private theorem hasDerivAt_affine_line (ξ h : ℂ) (s : ℝ) : HasDerivAt (fun s : ℝ => ξ + (s : ℂ) * h) h s := by
  simpa using ((TateReal.W3.hasDerivAt_ofReal' s).mul_const h).const_add ξ

private def gexpCD (α₁ : ℝ) (γr γi b₁ b₁' h ξ t : ℂ) : ℂ :=
  -(2 * Real.pi * α₁) * (h * starRingEnd ℂ ξ + ξ * starRingEnd ℂ h)
    + 2 * Real.pi * ((b₁ + (γr + γi * I) * starRingEnd ℂ t) * h
      + (b₁' + (starRingEnd ℂ γr + starRingEnd ℂ γi * I) * t) * starRingEnd ℂ h)

private theorem hasDerivAt_gexpC_line0 (α₁ α₂ : ℝ) (γr γi b₁ b₁' b₂ b₂' : ℂ) (h ξ t : ℂ) :
    HasDerivAt (fun s : ℝ => gexpC α₁ α₂ γr γi b₁ b₁' b₂ b₂' (ξ + (s : ℂ) * h) t)
      (gexpCD α₁ γr γi b₁ b₁' h ξ t) 0 := by
  have e : (fun s : ℝ => gexpC α₁ α₂ γr γi b₁ b₁' b₂ b₂' (ξ + (s : ℂ) * h) t)
      = fun s : ℝ => gexpC α₁ α₂ γr γi b₁ b₁' b₂ b₂' ξ t + (s : ℂ) * gexpCD α₁ γr γi b₁ b₁' h ξ t
          + (s : ℂ) ^ 2 * (-(2 * Real.pi * α₁) * (h * starRingEnd ℂ h)) := by
    funext s
    simp only [gexpC, gexpCD, ← Complex.mul_conj', map_add, map_mul, Complex.conj_ofReal]
    ring
  rw [e]
  have hs := TateReal.W3.hasDerivAt_ofReal' (0 : ℝ)
  have hd := ((hs.mul_const (gexpCD α₁ γr γi b₁ b₁' h ξ t)).const_add
      (gexpC α₁ α₂ γr γi b₁ b₁' b₂ b₂' ξ t)).add
    ((hs.pow 2).mul_const (-(2 * Real.pi * α₁) * (h * starRingEnd ℂ h)))
  convert hd using 1 <;> try rfl
  simp

private theorem hasDerivAt_genC_line0 (α₁ α₂ : ℝ) (γr γi b₁ b₁' b₂ b₂' : ℂ) (h ξ t : ℂ) :
    HasDerivAt (fun s : ℝ => genC α₁ α₂ γr γi b₁ b₁' b₂ b₂' (ξ + (s : ℂ) * h) t)
      (genC α₁ α₂ γr γi b₁ b₁' b₂ b₂' ξ t * gexpCD α₁ γr γi b₁ b₁' h ξ t) 0 := by
  have hd := (hasDerivAt_gexpC_line0 α₁ α₂ γr γi b₁ b₁' b₂ b₂' h ξ t).cexp
  convert hd using 1 <;> try rfl
  simp [genC]

private theorem ClsC.differentiableAt_line0 {Ψ : ℂ → ℂ → ℂ} (hΨ : ClsC Ψ) (h t ξ : ℂ) :
    DifferentiableAt ℝ (fun s : ℝ => Ψ (ξ + (s : ℂ) * h) t) 0 := by
  induction hΨ generalizing ξ with
  | gen b₁ b₁' b₂ b₂' _ => exact (hasDerivAt_genC_line0 _ _ _ _ b₁ b₁' b₂ b₂' h ξ t).differentiableAt
  | smul c _ ih => exact (ih ξ).const_mul c
  | add _ _ ih₁ ih₂ => exact (ih₁ ξ).add (ih₂ ξ)
  | mulZ _ ih => exact (hasDerivAt_affine_line ξ h 0).differentiableAt.mul (ih ξ)
  | @mulZbar Ψ _ ih =>
    have e : (fun s : ℝ => starRingEnd ℂ (ξ + (s : ℂ) * h) * Ψ (ξ + (s : ℂ) * h) t)
        = fun s : ℝ => (starRingEnd ℂ ξ + (s : ℂ) * starRingEnd ℂ h) * Ψ (ξ + (s : ℂ) * h) t := by
      funext s
      rw [map_add, map_mul, Complex.conj_ofReal]
    show DifferentiableAt ℝ (fun s : ℝ => starRingEnd ℂ (ξ + (s : ℂ) * h) * Ψ (ξ + (s : ℂ) * h) t) 0
    rw [e]
    exact (hasDerivAt_affine_line (starRingEnd ℂ ξ) (starRingEnd ℂ h) 0).differentiableAt.mul (ih ξ)
  | mulT _ ih => exact (ih ξ).const_mul t
  | mulTbar _ ih => exact (ih ξ).const_mul _

private theorem ClsC.closed_lineD {Ψ : ℂ → ℂ → ℂ} (hΨ : ClsC Ψ) (h : ℂ) : ClsC (lineD h Ψ) := by
  induction hΨ with
  | @gen α₁ α₂ γr γi b₁ b₁' b₂ b₂' hadm =>
    have key : lineD h (genC α₁ α₂ γr γi b₁ b₁' b₂ b₂')
        = fun ξ t => genC α₁ α₂ γr γi b₁ b₁' b₂ b₂' ξ t * gexpCD α₁ γr γi b₁ b₁' h ξ t := by
      funext ξ t
      exact (hasDerivAt_genC_line0 α₁ α₂ γr γi b₁ b₁' b₂ b₂' h ξ t).deriv
    rw [key]
    have G := ClsC.gen b₁ b₁' b₂ b₂' hadm
    refine ((G.mulZbar.smul (-(2 * Real.pi * α₁) * h)).add ((G.mulZ.smul (-(2 * Real.pi * α₁) * starRingEnd ℂ h)).add
      ((G.smul (2 * Real.pi * (b₁ * h + b₁' * starRingEnd ℂ h))).add
      ((G.mulTbar.smul (2 * Real.pi * h * (γr + γi * I))).add
      (G.mulT.smul (2 * Real.pi * starRingEnd ℂ h * (starRingEnd ℂ γr + starRingEnd ℂ γi * I))))))).congr ?_
    funext ξ t
    simp only [gexpCD]
    ring
  | @smul c Ψ hΨ ih =>
    have key : lineD h (fun z t => c * Ψ z t) = fun ξ t => c * lineD h Ψ ξ t := by
      funext ξ t
      exact deriv_const_mul c (hΨ.differentiableAt_line0 h t ξ)
    rw [key]
    exact ih.smul c
  | @add Ψ Φ hΨ hΦ ih₁ ih₂ =>
    have key : lineD h (fun z t => Ψ z t + Φ z t) = fun ξ t => lineD h Ψ ξ t + lineD h Φ ξ t := by
      funext ξ t
      exact deriv_add (hΨ.differentiableAt_line0 h t ξ) (hΦ.differentiableAt_line0 h t ξ)
    rw [key]
    exact ih₁.add ih₂
  | @mulZ Ψ hΨ ih =>
    have key : lineD h (fun z t => z * Ψ z t) = fun ξ t => h * Ψ ξ t + ξ * lineD h Ψ ξ t := by
      funext ξ t
      have hd : HasDerivAt (fun s : ℝ => (ξ + (s : ℂ) * h) * Ψ (ξ + (s : ℂ) * h) t)
          (h * Ψ (ξ + ((0 : ℝ) : ℂ) * h) t
            + (ξ + ((0 : ℝ) : ℂ) * h) * deriv (fun s : ℝ => Ψ (ξ + (s : ℂ) * h) t) 0) 0 :=
        (hasDerivAt_affine_line ξ h 0).mul (hΨ.differentiableAt_line0 h t ξ).hasDerivAt
      show deriv (fun s : ℝ => (ξ + (s : ℂ) * h) * Ψ (ξ + (s : ℂ) * h) t) 0 = _
      rw [hd.deriv]
      simp only [Complex.ofReal_zero, zero_mul, add_zero, lineD]
    rw [key]
    exact (hΨ.smul h).add ih.mulZ
  | @mulZbar Ψ hΨ ih =>
    have key : lineD h (fun z t => starRingEnd ℂ z * Ψ z t)
        = fun ξ t => starRingEnd ℂ h * Ψ ξ t + starRingEnd ℂ ξ * lineD h Ψ ξ t := by
      funext ξ t
      have e : (fun s : ℝ => starRingEnd ℂ (ξ + (s : ℂ) * h) * Ψ (ξ + (s : ℂ) * h) t)
          = fun s : ℝ => (starRingEnd ℂ ξ + (s : ℂ) * starRingEnd ℂ h) * Ψ (ξ + (s : ℂ) * h) t := by
        funext s
        rw [map_add, map_mul, Complex.conj_ofReal]
      have hd : HasDerivAt (fun s : ℝ => (starRingEnd ℂ ξ + (s : ℂ) * starRingEnd ℂ h) * Ψ (ξ + (s : ℂ) * h) t)
          (starRingEnd ℂ h * Ψ (ξ + ((0 : ℝ) : ℂ) * h) t
            + (starRingEnd ℂ ξ + ((0 : ℝ) : ℂ) * starRingEnd ℂ h) * deriv (fun s : ℝ => Ψ (ξ + (s : ℂ) * h) t) 0) 0 :=
        (hasDerivAt_affine_line (starRingEnd ℂ ξ) (starRingEnd ℂ h) 0).mul (hΨ.differentiableAt_line0 h t ξ).hasDerivAt
      show deriv (fun s : ℝ => starRingEnd ℂ (ξ + (s : ℂ) * h) * Ψ (ξ + (s : ℂ) * h) t) 0 = _
      rw [e, hd.deriv]
      simp only [Complex.ofReal_zero, zero_mul, add_zero, lineD]
    rw [key]
    exact (hΨ.smul _).add ih.mulZbar
  | @mulT Ψ hΨ ih =>
    have key : lineD h (fun z t => t * Ψ z t) = fun ξ t => t * lineD h Ψ ξ t := by
      funext ξ t
      exact deriv_const_mul t (hΨ.differentiableAt_line0 h t ξ)
    rw [key]
    exact ih.mulT
  | @mulTbar Ψ hΨ ih =>
    have key : lineD h (fun z t => starRingEnd ℂ t * Ψ z t) = fun ξ t => starRingEnd ℂ t * lineD h Ψ ξ t := by
      funext ξ t
      exact deriv_const_mul _ (hΨ.differentiableAt_line0 h t ξ)
    rw [key]
    exact ih.mulTbar

private theorem integrable_mul_psiComplex {f : ℂ → ℂ} (hf : Integrable f) (w : ℂ) :
    Integrable fun z : ℂ => f z * psiComplex (z * w) :=
  (hf.bdd_mul (c := 1) ((continuous_psiComplex.comp (continuous_id.mul continuous_const)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun _ => (norm_psiComplex _).le)).congr
    (Filter.Eventually.of_forall fun _ => mul_comm _ _)

private theorem F₁C_smul (c : ℂ) (Ψ : ℂ → ℂ → ℂ) : F₁C (fun z t => c * Ψ z t) = fun ξ t => c * F₁C Ψ ξ t := by
  funext ξ t
  exact congrFun (FC_const_mul c (fun z => Ψ z t)) (starRingEnd ℂ ξ)

private theorem F₁C_mulT (Ψ : ℂ → ℂ → ℂ) : F₁C (fun z t => t * Ψ z t) = fun ξ t => t * F₁C Ψ ξ t := by
  funext ξ t
  exact congrFun (FC_const_mul t (fun z => Ψ z t)) (starRingEnd ℂ ξ)

private theorem F₁C_mulTbar (Ψ : ℂ → ℂ → ℂ) :
    F₁C (fun z t => starRingEnd ℂ t * Ψ z t) = fun ξ t => starRingEnd ℂ t * F₁C Ψ ξ t := by
  funext ξ t
  exact congrFun (FC_const_mul (starRingEnd ℂ t) (fun z => Ψ z t)) (starRingEnd ℂ ξ)

private theorem F₁C_add {Ψ Φ : ℂ → ℂ → ℂ} (hΨ : ClsC Ψ) (hΦ : ClsC Φ) :
    F₁C (fun z t => Ψ z t + Φ z t) = fun ξ t => F₁C Ψ ξ t + F₁C Φ ξ t := by
  funext ξ t
  simp only [F₁C, FC, tateFourier]
  rw [← integral_add (integrable_mul_psiComplex (hΨ.integrable_sliceZ t) _)
    (integrable_mul_psiComplex (hΦ.integrable_sliceZ t) _)]
  congr 1
  funext z
  ring

private theorem F₁C_mulZ {Ψ : ℂ → ℂ → ℂ} (hΨ : ClsC Ψ) :
    F₁C (fun z t => z * Ψ z t)
      = fun ξ t => (-(4 * (Real.pi : ℂ) * I))⁻¹ * (lineD 1 (F₁C Ψ) ξ t + I * lineD I (F₁C Ψ) ξ t) := by
  funext ξ t
  have h := neg_four_pi_I_mul_FC_mul_left_conj (hΨ.integrable_sliceZ t) (hΨ.integrable_norm_mul_sliceZ t) ξ
  simp only [F₁C, lineD]
  rw [← h, ← mul_assoc, inv_mul_cancel₀ (neg_ne_zero.mpr four_pi_I_ne_zero), one_mul]

private theorem F₁C_mulZbar {Ψ : ℂ → ℂ → ℂ} (hΨ : ClsC Ψ) :
    F₁C (fun z t => starRingEnd ℂ z * Ψ z t)
      = fun ξ t => (-(4 * (Real.pi : ℂ) * I))⁻¹ * (lineD 1 (F₁C Ψ) ξ t + -I * lineD I (F₁C Ψ) ξ t) := by
  funext ξ t
  have h := neg_four_pi_I_mul_FC_conj_mul_left_conj (hΨ.integrable_sliceZ t) (hΨ.integrable_norm_mul_sliceZ t) ξ
  simp only [F₁C, lineD]
  rw [neg_mul, ← sub_eq_add_neg, ← h, ← mul_assoc, inv_mul_cancel₀ (neg_ne_zero.mpr four_pi_I_ne_zero),
    one_mul]

private theorem ClsC.F₁C {Ψ : ℂ → ℂ → ℂ} (hΨ : ClsC Ψ) : ClsC (F₁C Ψ) := by
  induction hΨ with
  | gen b₁ b₁' b₂ b₂' hadm =>
    rw [F₁C_genC b₁ b₁' b₂ b₂' hadm]
    exact (ClsC.gen _ _ _ _ hadm.transformed).smul _
  | smul c _ ih =>
    rw [F₁C_smul]
    exact ih.smul c
  | add hΨ hΦ ih₁ ih₂ =>
    rw [F₁C_add hΨ hΦ]
    exact ih₁.add ih₂
  | mulZ hΨ ih =>
    rw [F₁C_mulZ hΨ]
    exact ((ih.closed_lineD 1).add ((ih.closed_lineD I).smul I)).smul _
  | mulZbar hΨ ih =>
    rw [F₁C_mulZbar hΨ]
    exact ((ih.closed_lineD 1).add ((ih.closed_lineD I).smul (-I))).smul _
  | mulT _ ih =>
    rw [F₁C_mulT]
    exact ih.mulT
  | mulTbar _ ih =>
    rw [F₁C_mulTbar]
    exact ih.mulTbar

private theorem ClsC.F₂C {Ψ : ℂ → ℂ → ℂ} (hΨ : ClsC Ψ) : ClsC (F₂C Ψ) := by
  rw [F₂C_eq_swap_F₁C_swap]
  exact hΨ.swap.F₁C.swap

end W3C

end TateComplex

end

end

section

noncomputable section

open Complex MeasureTheory Set

namespace TateComplex

namespace W3C

private theorem ae_ne_zero_C : ∀ᵐ z : ℂ ∂(volume : Measure ℂ), z ≠ 0 := by
  rw [ae_iff]
  simp

private theorem ae_off_axes_C : ∀ᵐ p : ℂ × ℂ ∂((volume : Measure ℂ).prod volume), p.1 ≠ 0 ∧ p.2 ≠ 0 := by
  have hm : MeasurableSet {p : ℂ × ℂ | p.1 ≠ 0 ∧ p.2 ≠ 0} :=
    ((measurableSet_eq_fun measurable_fst measurable_const).compl).inter
      ((measurableSet_eq_fun measurable_snd measurable_const).compl)
  rw [Measure.ae_prod_iff_ae_ae hm]
  exact ae_ne_zero_C.mono fun z hz => ae_ne_zero_C.mono fun t ht => ⟨hz, ht⟩

private def profC (σlo σhi : ℝ) (z : ℂ) : ℝ :=
  (‖z‖ ^ 2) ^ (σlo - 1) + (‖z‖ ^ 2) ^ (σhi - 1) + (‖z‖ ^ 2) ^ (0 : ℝ)

private theorem profC_nonneg (σlo σhi : ℝ) (z : ℂ) : 0 ≤ profC σlo σhi z := by
  unfold profC; positivity

private theorem norm_kerC_le (k : ℤ) {w : ℂ} {σlo σhi : ℝ} (hlo : σlo ≤ w.re) (hhi : w.re ≤ σhi) {z : ℂ}
    (hz : z ≠ 0) : ‖kerC k w z‖ ≤ profC σlo σhi z := by
  unfold profC
  rw [norm_kerC hz]
  have hpos : 0 < ‖z‖ ^ 2 := pow_pos (norm_pos_iff.2 hz) 2
  have h0 : (0 : ℝ) ≤ (‖z‖ ^ 2) ^ (0 : ℝ) := by positivity
  rcases le_or_gt (‖z‖ ^ 2) 1 with h1 | h1
  · have : (‖z‖ ^ 2) ^ (w.re - 1) ≤ (‖z‖ ^ 2) ^ (σlo - 1) :=
      Real.rpow_le_rpow_of_exponent_ge hpos h1 (by linarith)
    have h2 : (0 : ℝ) ≤ (‖z‖ ^ 2) ^ (σhi - 1) := by positivity
    exact this.trans ((le_add_of_nonneg_right h2).trans (le_add_of_nonneg_right h0))
  · have : (‖z‖ ^ 2) ^ (w.re - 1) ≤ (‖z‖ ^ 2) ^ (σhi - 1) :=
      Real.rpow_le_rpow_of_exponent_le h1.le (by linarith)
    have h2 : (0 : ℝ) ≤ (‖z‖ ^ 2) ^ (σlo - 1) := by positivity
    exact this.trans ((le_add_of_nonneg_left h2).trans (le_add_of_nonneg_right h0))

private def domC (σlo σhi δ : ℝ) (z : ℂ) : ℝ := profC σlo σhi z * Real.exp (-δ * ‖z‖ ^ 2)

private theorem domC_nonneg (σlo σhi δ : ℝ) (z : ℂ) : 0 ≤ domC σlo σhi δ z :=
  mul_nonneg (profC_nonneg σlo σhi z) (Real.exp_pos _).le

private def radG (σlo σhi δ : ℝ) (r : ℝ) : ℝ :=
  r ^ (0 : ℕ) * (r ^ 2) ^ (σlo - 1) * Real.exp (-δ * r ^ 2 + 0 * r)
    + r ^ (0 : ℕ) * (r ^ 2) ^ (σhi - 1) * Real.exp (-δ * r ^ 2 + 0 * r)
    + r ^ (0 : ℕ) * (r ^ 2) ^ (0 : ℝ) * Real.exp (-δ * r ^ 2 + 0 * r)

private theorem radG_nonneg (σlo σhi δ : ℝ) {r : ℝ} (_hr : 0 ≤ r) : 0 ≤ radG σlo σhi δ r := by
  unfold radG; positivity

private theorem domC_eq_radG (σlo σhi δ : ℝ) (z : ℂ) : domC σlo σhi δ z = radG σlo σhi δ ‖z‖ := by
  simp only [domC, profC, radG, pow_zero, one_mul, zero_mul, add_zero]
  ring

private theorem integrableOn_mul_radG {σlo σhi δ : ℝ} (hlo : 0 < σlo) (hhi : 0 < σhi) (hδ : 0 < δ) :
    IntegrableOn (fun r : ℝ => r * radG σlo σhi δ r) (Ioi 0) := by
  have h1 := integrableOn_radial_term hδ 0 0 (a := σlo - 1) (by linarith)
  have h2 := integrableOn_radial_term hδ 0 0 (a := σhi - 1) (by linarith)
  have h3 := integrableOn_radial_term hδ 0 0 (a := 0) (by norm_num)
  refine ((h1.add h2).add h3).congr_fun (fun r _ => ?_) measurableSet_Ioi
  simp only [radG, Pi.add_apply]
  ring

private theorem measurable_domC (σlo σhi δ : ℝ) : Measurable (domC σlo σhi δ) := by
  unfold domC profC
  have hn : Measurable fun z : ℂ => ‖z‖ ^ 2 := (continuous_norm.pow 2).measurable
  exact (((hn.pow_const _).add (hn.pow_const _)).add (hn.pow_const _)).mul
    (Real.measurable_exp.comp (hn.const_mul _))

private theorem integrable_domC {σlo σhi δ : ℝ} (hlo : 0 < σlo) (hhi : 0 < σhi) (hδ : 0 < δ) :
    Integrable (domC σlo σhi δ) := by
  have hF : Integrable (fun z : ℂ => ((domC σlo σhi δ z : ℝ) : ℂ)) := by
    refine integrable_of_radial_bound (G := radG σlo σhi δ)
      (Complex.measurable_ofReal.comp (measurable_domC σlo σhi δ)).aestronglyMeasurable
      (integrableOn_mul_radG hlo hhi hδ) (fun r hr => radG_nonneg σlo σhi δ (mem_Ioi.mp hr).le)
      fun z _ => ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (domC_nonneg σlo σhi δ z), domC_eq_radG]
  simpa using hF.re

private theorem ClsC.bound' {Ψ : ℂ → ℂ → ℂ} (h : ClsC Ψ) :
    ∃ (C δ : ℝ), 0 ≤ C ∧ 0 < δ ∧
      ∀ z t : ℂ, ‖Ψ z t‖ ≤ C * (Real.exp (-δ * ‖z‖ ^ 2) * Real.exp (-δ * ‖t‖ ^ 2)) := by
  obtain ⟨C, N, δ, hC, hδ, hb⟩ := h.bound
  refine ⟨C * (N.factorial * Real.exp (1 + 1 / δ)), δ / 2, by positivity, by positivity, fun z t => ?_⟩
  have hpoly : (1 + ‖z‖ + ‖t‖) ^ N ≤ N.factorial * Real.exp (1 + ‖z‖ + ‖t‖) := by
    have h := Real.pow_div_factorial_le_exp (x := 1 + ‖z‖ + ‖t‖) (by positivity) N
    have hf : (0 : ℝ) < N.factorial := by exact_mod_cast N.factorial_pos
    rwa [div_le_iff₀ hf, mul_comm] at h
  have ham : ∀ r : ℝ, 0 ≤ r → r ≤ δ / 2 * r ^ 2 + 1 / (2 * δ) := fun r _ => by
    rw [← sub_nonneg]
    have e : δ / 2 * r ^ 2 + 1 / (2 * δ) - r = (δ * r - 1) ^ 2 / (2 * δ) := by
      field_simp
      ring
    rw [e]
    positivity
  have hamz := ham ‖z‖ (norm_nonneg z)
  have hamt := ham ‖t‖ (norm_nonneg t)
  have hexp : Real.exp (1 + ‖z‖ + ‖t‖) * Real.exp (-δ * (‖z‖ ^ 2 + ‖t‖ ^ 2))
      ≤ Real.exp (1 + 1 / δ) * (Real.exp (-(δ / 2) * ‖z‖ ^ 2) * Real.exp (-(δ / 2) * ‖t‖ ^ 2)) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have e : 1 / δ = 1 / (2 * δ) + 1 / (2 * δ) := by field_simp; ring
    nlinarith [hamz, hamt, e]
  calc ‖Ψ z t‖ ≤ C * (1 + ‖z‖ + ‖t‖) ^ N * Real.exp (-δ * (‖z‖ ^ 2 + ‖t‖ ^ 2)) := hb z t
    _ ≤ C * (N.factorial * Real.exp (1 + ‖z‖ + ‖t‖)) * Real.exp (-δ * (‖z‖ ^ 2 + ‖t‖ ^ 2)) := by gcongr
    _ = C * N.factorial * (Real.exp (1 + ‖z‖ + ‖t‖) * Real.exp (-δ * (‖z‖ ^ 2 + ‖t‖ ^ 2))) := by ring
    _ ≤ C * N.factorial * (Real.exp (1 + 1 / δ)
          * (Real.exp (-(δ / 2) * ‖z‖ ^ 2) * Real.exp (-(δ / 2) * ‖t‖ ^ 2))) := by gcongr
    _ = C * (N.factorial * Real.exp (1 + 1 / δ))
          * (Real.exp (-(δ / 2) * ‖z‖ ^ 2) * Real.exp (-(δ / 2) * ‖t‖ ^ 2)) := by ring

private def zintC (Ψ : ℂ → ℂ → ℂ) (k₁ k₂ : ℤ) (w₁ w₂ : ℂ) (p : ℂ × ℂ) : ℂ :=
  Ψ p.1 p.2 * kerC k₁ w₁ p.1 * kerC k₂ w₂ p.2

private def ZC (Ψ : ℂ → ℂ → ℂ) (k₁ k₂ : ℤ) (w₁ w₂ : ℂ) : ℂ := ∫ p : ℂ × ℂ, zintC Ψ k₁ k₂ w₁ w₂ p

private theorem ClsC.aestronglyMeasurable_zintC {Ψ : ℂ → ℂ → ℂ} (h : ClsC Ψ) (k₁ k₂ : ℤ) (w₁ w₂ : ℂ) :
    AEStronglyMeasurable (zintC Ψ k₁ k₂ w₁ w₂) ((volume : Measure ℂ).prod volume) :=
  ((h.continuous.measurable.mul ((measurable_kerC k₁ w₁).comp measurable_fst)).mul
    ((measurable_kerC k₂ w₂).comp measurable_snd)).aestronglyMeasurable

private theorem ClsC.exists_dominator {Ψ : ℂ → ℂ → ℂ} (h : ClsC Ψ) {σlo σhi : ℝ} (hlo : 0 < σlo) (hhi : 0 < σhi) :
    ∃ D : ℂ → ℝ, Integrable D ∧ (∀ z, 0 ≤ D z) ∧
      ∀ (k₁ k₂ : ℤ) (w₁ w₂ : ℂ), σlo ≤ w₁.re → w₁.re ≤ σhi → σlo ≤ w₂.re → w₂.re ≤ σhi →
        ∀ p : ℂ × ℂ, p.1 ≠ 0 → p.2 ≠ 0 → ‖zintC Ψ k₁ k₂ w₁ w₂ p‖ ≤ D p.1 * D p.2 := by
  obtain ⟨C, δ, hC, hδ, hb⟩ := h.bound'
  refine ⟨fun z => Real.sqrt C * domC σlo σhi δ z, (integrable_domC hlo hhi hδ).const_mul _,
    fun z => mul_nonneg (Real.sqrt_nonneg _) (domC_nonneg σlo σhi δ z),
    fun k₁ k₂ w₁ w₂ h1 h2 h3 h4 p hp₁ hp₂ => ?_⟩
  simp only [zintC, domC]
  rw [norm_mul, norm_mul]
  have hk₁ := norm_kerC_le k₁ h1 h2 hp₁
  have hk₂ := norm_kerC_le k₂ h3 h4 hp₂
  have hsq : Real.sqrt C * Real.sqrt C = C := Real.mul_self_sqrt hC
  have hE : (0 : ℝ) ≤ C * (Real.exp (-δ * ‖p.1‖ ^ 2) * Real.exp (-δ * ‖p.2‖ ^ 2)) := by positivity
  calc ‖Ψ p.1 p.2‖ * ‖kerC k₁ w₁ p.1‖ * ‖kerC k₂ w₂ p.2‖
      ≤ (C * (Real.exp (-δ * ‖p.1‖ ^ 2) * Real.exp (-δ * ‖p.2‖ ^ 2)))
          * profC σlo σhi p.1 * profC σlo σhi p.2 :=
        mul_le_mul (mul_le_mul (hb p.1 p.2) hk₁ (norm_nonneg _) hE) hk₂ (norm_nonneg _)
          (mul_nonneg hE (profC_nonneg _ _ _))
    _ = Real.sqrt C * (profC σlo σhi p.1 * Real.exp (-δ * ‖p.1‖ ^ 2))
          * (Real.sqrt C * (profC σlo σhi p.2 * Real.exp (-δ * ‖p.2‖ ^ 2))) := by
        linear_combination (-(Real.exp (-δ * ‖p.1‖ ^ 2) * Real.exp (-δ * ‖p.2‖ ^ 2) * profC σlo σhi p.1
          * profC σlo σhi p.2)) * hsq

private theorem ClsC.integrable_zintC {Ψ : ℂ → ℂ → ℂ} (h : ClsC Ψ) (k₁ k₂ : ℤ) {w₁ w₂ : ℂ} (h₁ : 0 < w₁.re)
    (h₂ : 0 < w₂.re) : Integrable (zintC Ψ k₁ k₂ w₁ w₂) ((volume : Measure ℂ).prod volume) := by
  obtain ⟨D, hD, hD0, hbound⟩ := h.exists_dominator (σlo := min w₁.re w₂.re) (σhi := max w₁.re w₂.re)
    (lt_min h₁ h₂) (lt_max_of_lt_left h₁)
  refine (hD.mul_prod hD).mono' (h.aestronglyMeasurable_zintC k₁ k₂ w₁ w₂) (ae_off_axes_C.mono fun p hp => ?_)
  exact hbound k₁ k₂ w₁ w₂ (min_le_left _ _) (le_max_left _ _) (min_le_right _ _) (le_max_right _ _) p hp.1 hp.2

private theorem ZC_swap (Ψ : ℂ → ℂ → ℂ) (k₁ k₂ : ℤ) (w₁ w₂ : ℂ) :
    ZC (fun z t => Ψ t z) k₂ k₁ w₂ w₁ = ZC Ψ k₁ k₂ w₁ w₂ := by
  unfold ZC
  rw [Measure.volume_eq_prod, ← integral_prod_swap (zintC Ψ k₁ k₂ w₁ w₂)]
  congr 1
  funext p
  simp only [zintC, Prod.fst_swap, Prod.snd_swap]
  ring

private theorem ZC_smul (c : ℂ) (Ψ : ℂ → ℂ → ℂ) (k₁ k₂ : ℤ) (w₁ w₂ : ℂ) :
    ZC (fun z t => c * Ψ z t) k₁ k₂ w₁ w₂ = c * ZC Ψ k₁ k₂ w₁ w₂ := by
  unfold ZC
  rw [← integral_const_mul]
  congr 1
  funext p
  simp only [zintC]
  ring

private theorem ClsC.ZC_eq_iterated {Ψ : ℂ → ℂ → ℂ} (h : ClsC Ψ) (k₁ k₂ : ℤ) {w₁ w₂ : ℂ} (h₁ : 0 < w₁.re)
    (h₂ : 0 < w₂.re) :
    ZC Ψ k₁ k₂ w₁ w₂ = ∫ t : ℂ, tateZetaC (fun z => Ψ z t) k₁ w₁ * kerC k₂ w₂ t := by
  unfold ZC
  rw [Measure.volume_eq_prod, integral_prod_symm _ (h.integrable_zintC k₁ k₂ h₁ h₂)]
  congr 1
  funext t
  simp only [zintC]
  rw [tateZetaC_eq_integral_ker]
  exact integral_mul_const (kerC k₂ w₂ t) (fun z => Ψ z t * kerC k₁ w₁ z)

private theorem ClsC.exists_ZC_bound {Ψ : ℂ → ℂ → ℂ} (h : ClsC Ψ) {σlo σhi : ℝ} (hlo : 0 < σlo) (hhi : 0 < σhi) :
    ∃ M : ℝ, ∀ (k₁ k₂ : ℤ) (w₁ w₂ : ℂ), σlo ≤ w₁.re → w₁.re ≤ σhi → σlo ≤ w₂.re → w₂.re ≤ σhi →
      ‖ZC Ψ k₁ k₂ w₁ w₂‖ ≤ M := by
  obtain ⟨D, hD, _, hbound⟩ := h.exists_dominator hlo hhi
  refine ⟨∫ p : ℂ × ℂ, D p.1 * D p.2 ∂((volume : Measure ℂ).prod volume), fun k₁ k₂ w₁ w₂ h1 h2 h3 h4 => ?_⟩
  unfold ZC
  rw [Measure.volume_eq_prod]
  exact norm_integral_le_of_norm_le (hD.mul_prod hD)
    (ae_off_axes_C.mono fun p hp => hbound k₁ k₂ w₁ w₂ h1 h2 h3 h4 p hp.1 hp.2)

end W3C

end TateComplex

end

end

section

noncomputable section

open Complex MeasureTheory Set LanglandsTunnell.TateLocal LanglandsTunnell.ArchPlace

namespace TateComplex

namespace W3C

private theorem FC_add' {f g : ℂ → ℂ} (hf : Integrable f) (hg : Integrable g) :
    FC (fun z => f z + g z) = fun w => FC f w + FC g w := by
  funext w
  simp only [FC, tateFourier]
  rw [← integral_add (integrable_mul_psiComplex hf _) (integrable_mul_psiComplex hg _)]
  congr 1
  funext z
  ring

private theorem tateZetaC_add {f g : ℂ → ℂ} (k : ℤ) (s : ℂ) (hf : Integrable (fun z : ℂ => f z * kerC k s z))
    (hg : Integrable (fun z : ℂ => g z * kerC k s z)) :
    tateZetaC (fun z => f z + g z) k s = tateZetaC f k s + tateZetaC g k s := by
  rw [tateZetaC_eq_integral_ker, tateZetaC_eq_integral_ker, tateZetaC_eq_integral_ker, ← integral_add hf hg]
  congr 1
  funext z
  ring

private theorem tateZetaC_const_mul' (c : ℂ) (f : ℂ → ℂ) (k : ℤ) (s : ℂ) :
    tateZetaC (fun z => c * f z) k s = c * tateZetaC f k s := by
  rw [tateZetaC_eq_integral_ker, tateZetaC_eq_integral_ker, ← integral_const_mul]
  congr 1
  funext z
  ring

private theorem kerC_conj {z : ℂ} (hz : z ≠ 0) (k : ℤ) (w : ℂ) : kerC k w (starRingEnd ℂ z) = kerC (-k) w z := by
  unfold kerC
  rw [Complex.norm_conj]
  have hz' : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hz
  have hu : z / (‖z‖ : ℂ) * (starRingEnd ℂ z / (‖z‖ : ℂ)) = 1 := by
    rw [div_mul_div_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow, pow_two,
      div_self (mul_ne_zero hz' hz')]
  rw [eq_inv_of_mul_eq_one_right hu, inv_zpow']

private theorem tateZetaC_comp_conj (g : ℂ → ℂ) (k : ℤ) (w : ℂ) :
    tateZetaC (fun ξ => g (starRingEnd ℂ ξ)) k w = tateZetaC g (-k) w := by
  rw [tateZetaC_eq_integral_ker, tateZetaC_eq_integral_ker]
  have hmp : MeasurePreserving (Complex.conjLIE : ℂ → ℂ) volume volume := Complex.conjLIE.measurePreserving
  have e : (fun ξ : ℂ => g (starRingEnd ℂ ξ) * kerC k w ξ)
      = fun ξ : ℂ => (fun y : ℂ => g y * kerC k w (starRingEnd ℂ y)) (Complex.conjLIE ξ) := by
    funext ξ
    simp only [Complex.conjLIE_apply, Complex.conj_conj]
  rw [e, hmp.integral_comp Complex.conjLIE.toHomeomorph.measurableEmbedding
    (fun y : ℂ => g y * kerC k w (starRingEnd ℂ y))]
  refine integral_congr_ae (ae_ne_zero_C.mono fun y hy => ?_)
  simp only [kerC_conj hy]

private theorem InSpanC.integrable_tate {f : ℂ → ℂ} (h : InSpanC f) (k : ℤ) {s : ℂ} (hs : 0 < s.re) :
    Integrable (fun z : ℂ => f z * kerC k s z) := by
  induction h with
  | mem hf => exact integrable_tateC hf k hs
  | smul c _ ih =>
    refine (ih.const_mul c).congr (Filter.Eventually.of_forall fun z => ?_)
    simp only
    ring
  | add _ _ ih₁ ih₂ =>
    refine (ih₁.add ih₂).congr (Filter.Eventually.of_forall fun z => ?_)
    simp only [Pi.add_apply]
    ring

private theorem InSpanC.FC_mem {f : ℂ → ℂ} (h : InSpanC f) : InSpanC (FC f) := by
  induction h with
  | mem hf => exact InSpanC.mem hf.FC
  | smul c _ ih =>
    rw [FC_const_mul]
    exact ih.smul c
  | add hf hg ih₁ ih₂ =>
    rw [FC_add' hf.integrable hg.integrable]
    exact ih₁.add ih₂

private theorem InSpanC.fe {f : ℂ → ℂ} (h : InSpanC f) (k : ℤ) {s : ℂ} (hs₀ : 0 < s.re) (hs₁ : s.re < 1) :
    tateZetaC (FC f) (-k) (1 - s) * Gammaℂ (s + (k.natAbs : ℂ) / 2)
      = cC k * Gammaℂ (1 - s + (k.natAbs : ℂ) / 2) * tateZetaC f k s := by
  have h1s : 0 < (1 - s).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
  induction h with
  | mem hf => exact strip_functional_equation_C hf k hs₀ hs₁
  | smul c _ ih =>
    rw [FC_const_mul, tateZetaC_const_mul', tateZetaC_const_mul']
    linear_combination c * ih
  | add hf hg ih₁ ih₂ =>
    rw [FC_add' hf.integrable hg.integrable,
      tateZetaC_add (-k) (1 - s) (hf.FC_mem.integrable_tate (-k) h1s) (hg.FC_mem.integrable_tate (-k) h1s),
      tateZetaC_add k s (hf.integrable_tate k hs₀) (hg.integrable_tate k hs₀)]
    linear_combination ih₁ + ih₂

private theorem ClsC.ZC_F₁C {Ψ : ℂ → ℂ → ℂ} (h : ClsC Ψ) (k₁ k₂ : ℤ) {w₁ w₂ : ℂ} (h0 : 0 < w₁.re) (h1 : w₁.re < 1)
    (h2 : 0 < w₂.re) :
    ZC (W3C.F₁C Ψ) k₁ k₂ (1 - w₁) w₂ * Gammaℂ (w₁ + (k₁.natAbs : ℂ) / 2)
      = cC k₁ * Gammaℂ (1 - w₁ + (k₁.natAbs : ℂ) / 2) * ZC Ψ k₁ k₂ w₁ w₂ := by
  have h1' : 0 < (1 - w₁).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
  rw [h.F₁C.ZC_eq_iterated k₁ k₂ h1' h2, h.ZC_eq_iterated k₁ k₂ h0 h2, ← integral_mul_const,
    ← integral_const_mul]
  congr 1
  funext t
  have hfe := (h.sliceZ t).fe k₁ h0 h1
  have e : tateZetaC (fun ξ => W3C.F₁C Ψ ξ t) k₁ (1 - w₁) = tateZetaC (FC fun z => Ψ z t) (-k₁) (1 - w₁) :=
    tateZetaC_comp_conj (FC fun z => Ψ z t) k₁ (1 - w₁)
  rw [e]
  linear_combination (kerC k₂ w₂ t) * hfe

private theorem ClsC.ZC_F₂C {Ψ : ℂ → ℂ → ℂ} (h : ClsC Ψ) (k₁ k₂ : ℤ) {w₁ w₂ : ℂ} (h1 : 0 < w₁.re) (h0 : 0 < w₂.re)
    (h2 : w₂.re < 1) :
    ZC (W3C.F₂C Ψ) k₁ k₂ w₁ (1 - w₂) * Gammaℂ (w₂ + (k₂.natAbs : ℂ) / 2)
      = cC k₂ * Gammaℂ (1 - w₂ + (k₂.natAbs : ℂ) / 2) * ZC Ψ k₁ k₂ w₁ w₂ := by
  rw [← ZC_swap Ψ, F₂C_eq_swap_F₁C_swap, ← ZC_swap]
  exact h.swap.ZC_F₁C k₂ k₁ h0 h2 h1

end W3C

end TateComplex

end

end

section

noncomputable section

open Complex MeasureTheory Set LanglandsTunnell.TateLocal LanglandsTunnell.ArchPlace

namespace TateComplex

namespace W3C

private theorem integrable_rpow_mul_gauss {a δ : ℝ} (ha : -1 < a) (hδ : 0 < δ) :
    Integrable (fun z : ℂ => (‖z‖ ^ 2) ^ a * Real.exp (-δ * ‖z‖ ^ 2)) := by
  have hF : Integrable (fun z : ℂ => (((‖z‖ ^ 2) ^ a * Real.exp (-δ * ‖z‖ ^ 2) : ℝ) : ℂ)) := by
    refine integrable_of_radial_bound
      (G := fun r : ℝ => r ^ (0 : ℕ) * (r ^ 2) ^ a * Real.exp (-δ * r ^ 2 + 0 * r)) ?_
      (integrableOn_radial_term hδ 0 0 ha) (fun r _ => by positivity) fun z _ => ?_
    · have hn : Measurable fun z : ℂ => ‖z‖ ^ 2 := (continuous_norm.pow 2).measurable
      exact (Complex.measurable_ofReal.comp
        ((hn.pow_const _).mul (Real.measurable_exp.comp (hn.const_mul _)))).aestronglyMeasurable
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      simp only [pow_zero, one_mul, zero_mul, add_zero]
      exact le_rfl
  simpa only [RCLike.re_to_complex, Complex.ofReal_re] using hF.re

private def logprofC (σlo σhi : ℝ) (z : ℂ) : ℝ :=
  ((‖z‖ ^ 2) ^ (σlo - 1 + σlo / 2) + (‖z‖ ^ 2) ^ (σhi - 1 + σlo / 2)
    + ((‖z‖ ^ 2) ^ (σlo - 1 - σlo / 2) + (‖z‖ ^ 2) ^ (σhi - 1 - σlo / 2))) / (σlo / 2)

private theorem logprofC_nonneg {σlo : ℝ} (hlo : 0 < σlo) (σhi : ℝ) (z : ℂ) : 0 ≤ logprofC σlo σhi z := by
  unfold logprofC; positivity

private theorem norm_kerC_mul_abs_log_le (k : ℤ) {w : ℂ} {σlo σhi : ℝ} (h0 : 0 < σlo) (hlo : σlo ≤ w.re)
    (hhi : w.re ≤ σhi) {z : ℂ} (hz : z ≠ 0) :
    ‖kerC k w z‖ * |Real.log (‖z‖ ^ 2)| ≤ logprofC σlo σhi z := by
  have hr : 0 < ‖z‖ ^ 2 := pow_pos (norm_pos_iff.2 hz) 2
  have hη : 0 < σlo / 2 := by positivity
  unfold logprofC
  rw [norm_kerC hz]
  calc (‖z‖ ^ 2) ^ (w.re - 1) * |Real.log (‖z‖ ^ 2)|
      ≤ (‖z‖ ^ 2) ^ (w.re - 1) * (((‖z‖ ^ 2) ^ (σlo / 2) + (‖z‖ ^ 2) ^ (-(σlo / 2))) / (σlo / 2)) :=
        mul_le_mul_of_nonneg_left (TateReal.W3.abs_log_le_rpow_add_rpow_div hr hη) (by positivity)
    _ = ((‖z‖ ^ 2) ^ (w.re - 1 + σlo / 2) + (‖z‖ ^ 2) ^ (w.re - 1 - σlo / 2)) / (σlo / 2) := by
        rw [Real.rpow_add hr, show w.re - 1 - σlo / 2 = (w.re - 1) + (-(σlo / 2)) by ring, Real.rpow_add hr]
        ring
    _ ≤ (((‖z‖ ^ 2) ^ (σlo - 1 + σlo / 2) + (‖z‖ ^ 2) ^ (σhi - 1 + σlo / 2))
          + ((‖z‖ ^ 2) ^ (σlo - 1 - σlo / 2) + (‖z‖ ^ 2) ^ (σhi - 1 - σlo / 2))) / (σlo / 2) := by
        gcongr
        · exact TateReal.W3.rpow_le_rpow_add_rpow hr (by linarith) (by linarith)
        · exact TateReal.W3.rpow_le_rpow_add_rpow hr (by linarith) (by linarith)

private def bigprofC (σlo σhi : ℝ) (z : ℂ) : ℝ := profC σlo σhi z + logprofC σlo σhi z

private theorem bigprofC_nonneg {σlo : ℝ} (hlo : 0 < σlo) (σhi : ℝ) (z : ℂ) : 0 ≤ bigprofC σlo σhi z :=
  add_nonneg (profC_nonneg _ _ _) (logprofC_nonneg hlo _ _)

private theorem integrable_bigprofC_mul_exp {σlo σhi δ : ℝ} (hlo : 0 < σlo) (hhi : σlo ≤ σhi) (hδ : 0 < δ) :
    Integrable (fun z : ℂ => bigprofC σlo σhi z * Real.exp (-δ * ‖z‖ ^ 2)) := by
  have p1 := integrable_rpow_mul_gauss (a := σlo - 1) (by linarith) hδ
  have p2 := integrable_rpow_mul_gauss (a := σhi - 1) (by linarith) hδ
  have p3 := integrable_rpow_mul_gauss (a := 0) (by norm_num) hδ
  have h1 := integrable_rpow_mul_gauss (a := σlo - 1 + σlo / 2) (by linarith) hδ
  have h2 := integrable_rpow_mul_gauss (a := σhi - 1 + σlo / 2) (by linarith) hδ
  have h3 := integrable_rpow_mul_gauss (a := σlo - 1 - σlo / 2) (by linarith) hδ
  have h4 := integrable_rpow_mul_gauss (a := σhi - 1 - σlo / 2) (by linarith) hδ
  have hL := ((h1.add h2).add (h3.add h4)).const_mul (σlo / 2)⁻¹
  refine (((p1.add p2).add p3).add hL).congr (Filter.Eventually.of_forall fun z => ?_)
  simp only [bigprofC, profC, logprofC, Pi.add_apply]
  field_simp

private def zintDC (Ψ : ℂ → ℂ → ℂ) (k₁ k₂ : ℤ) (l₁ c₁ l₂ c₂ : ℂ) (w : ℂ) (p : ℂ × ℂ) : ℂ :=
  zintC Ψ k₁ k₂ (l₁ * w + c₁) (l₂ * w + c₂) p
    * (l₁ * Complex.log (((‖p.1‖ ^ 2 : ℝ)) : ℂ) + l₂ * Complex.log (((‖p.2‖ ^ 2 : ℝ)) : ℂ))

private theorem hasDerivAt_kerC_line (k : ℤ) (l c : ℂ) (w : ℂ) {z : ℂ} (hz : z ≠ 0) :
    HasDerivAt (fun w : ℂ => kerC k (l * w + c) z)
      (kerC k (l * w + c) z * Complex.log (((‖z‖ ^ 2 : ℝ)) : ℂ) * l) w := by
  have hf : HasDerivAt (fun w : ℂ => l * w + c - 1) l w := by
    simpa using (((hasDerivAt_id w).const_mul l).add_const c).sub_const 1
  have h0 : (((‖z‖ ^ 2 : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast (pow_pos (norm_pos_iff.2 hz) 2).ne'
  have h := (hf.const_cpow (Or.inl h0)).const_mul ((z / (‖z‖ : ℂ)) ^ k)
  unfold kerC
  exact h.congr_deriv (by ring)

private theorem hasDerivAt_zintC_line (Ψ : ℂ → ℂ → ℂ) (k₁ k₂ : ℤ) (l₁ c₁ l₂ c₂ : ℂ) {p : ℂ × ℂ} (h1 : p.1 ≠ 0)
    (h2 : p.2 ≠ 0) (w : ℂ) :
    HasDerivAt (fun w : ℂ => zintC Ψ k₁ k₂ (l₁ * w + c₁) (l₂ * w + c₂) p) (zintDC Ψ k₁ k₂ l₁ c₁ l₂ c₂ w p) w := by
  have hk₁ := (hasDerivAt_kerC_line k₁ l₁ c₁ w h1).const_mul (Ψ p.1 p.2)
  have h : HasDerivAt (fun w : ℂ => Ψ p.1 p.2 * kerC k₁ (l₁ * w + c₁) p.1 * kerC k₂ (l₂ * w + c₂) p.2)
      (Ψ p.1 p.2 * (kerC k₁ (l₁ * w + c₁) p.1 * Complex.log (((‖p.1‖ ^ 2 : ℝ)) : ℂ) * l₁)
          * kerC k₂ (l₂ * w + c₂) p.2
        + Ψ p.1 p.2 * kerC k₁ (l₁ * w + c₁) p.1
          * (kerC k₂ (l₂ * w + c₂) p.2 * Complex.log (((‖p.2‖ ^ 2 : ℝ)) : ℂ) * l₂)) w :=
    hk₁.mul (hasDerivAt_kerC_line k₂ l₂ c₂ w h2)
  unfold zintDC zintC
  exact h.congr_deriv (by ring)

private theorem norm_log_ofReal_norm_sq (z : ℂ) : ‖Complex.log (((‖z‖ ^ 2 : ℝ)) : ℂ)‖ = |Real.log (‖z‖ ^ 2)| := by
  rw [← Complex.ofReal_log (by positivity), Complex.norm_real, Real.norm_eq_abs]

private theorem ClsC.aestronglyMeasurable_zintDC {Ψ : ℂ → ℂ → ℂ} (h : ClsC Ψ) (k₁ k₂ : ℤ) (l₁ c₁ l₂ c₂ w : ℂ) :
    AEStronglyMeasurable (zintDC Ψ k₁ k₂ l₁ c₁ l₂ c₂ w) ((volume : Measure ℂ).prod volume) := by
  have hsq : Measurable fun z : ℂ => (((‖z‖ ^ 2 : ℝ)) : ℂ) :=
    Complex.measurable_ofReal.comp (continuous_norm.pow 2).measurable
  have hlog : Measurable fun p : ℂ × ℂ =>
      l₁ * Complex.log (((‖p.1‖ ^ 2 : ℝ)) : ℂ) + l₂ * Complex.log (((‖p.2‖ ^ 2 : ℝ)) : ℂ) :=
    ((Complex.measurable_log.comp (hsq.comp measurable_fst)).const_mul l₁).add
      ((Complex.measurable_log.comp (hsq.comp measurable_snd)).const_mul l₂)
  exact (h.aestronglyMeasurable_zintC k₁ k₂ _ _).mul hlog.aestronglyMeasurable

private theorem ClsC.exists_dominatorD {Ψ : ℂ → ℂ → ℂ} (h : ClsC Ψ) {σlo σhi : ℝ} (hlo : 0 < σlo) (hhi : σlo ≤ σhi)
    (k₁ k₂ : ℤ) (l₁ c₁ l₂ c₂ : ℂ) :
    ∃ D : ℂ → ℝ, Integrable D ∧
      ∀ w : ℂ, σlo ≤ (l₁ * w + c₁).re → (l₁ * w + c₁).re ≤ σhi → σlo ≤ (l₂ * w + c₂).re → (l₂ * w + c₂).re ≤ σhi →
        ∀ p : ℂ × ℂ, p.1 ≠ 0 → p.2 ≠ 0 → ‖zintDC Ψ k₁ k₂ l₁ c₁ l₂ c₂ w p‖ ≤ D p.1 * D p.2 := by
  obtain ⟨C, δ, hC, hδ, hb⟩ := h.bound'
  have hL0 : 0 ≤ ‖l₁‖ + ‖l₂‖ := by positivity
  have hK0 : 0 ≤ C * (‖l₁‖ + ‖l₂‖) := mul_nonneg hC hL0
  refine ⟨fun z => Real.sqrt (C * (‖l₁‖ + ‖l₂‖)) * (bigprofC σlo σhi z * Real.exp (-δ * ‖z‖ ^ 2)),
    (integrable_bigprofC_mul_exp hlo hhi hδ).const_mul _, fun w h1 h2 h3 h4 p hp1 hp2 => ?_⟩
  have hk₁ := norm_kerC_le k₁ h1 h2 hp1
  have hk₂ := norm_kerC_le k₂ h3 h4 hp2
  have hkl₁ := norm_kerC_mul_abs_log_le k₁ hlo h1 h2 hp1
  have hkl₂ := norm_kerC_mul_abs_log_le k₂ hlo h3 h4 hp2
  have hΨ := hb p.1 p.2
  have hp₁ := profC_nonneg σlo σhi p.1
  have hp₂ := profC_nonneg σlo σhi p.2
  have hl₁ := logprofC_nonneg hlo σhi p.1
  have hl₂ := logprofC_nonneg hlo σhi p.2
  have hn₁ := norm_nonneg (kerC k₁ (l₁ * w + c₁) p.1)
  have hn₂ := norm_nonneg (kerC k₂ (l₂ * w + c₂) p.2)
  have hlog₁ := abs_nonneg (Real.log (‖p.1‖ ^ 2))
  have hlog₂ := abs_nonneg (Real.log (‖p.2‖ ^ 2))
  have hE₁ := (Real.exp_pos (-δ * ‖p.1‖ ^ 2)).le
  have hE₂ := (Real.exp_pos (-δ * ‖p.2‖ ^ 2)).le

  have hlogfac : ‖l₁ * Complex.log (((‖p.1‖ ^ 2 : ℝ)) : ℂ) + l₂ * Complex.log (((‖p.2‖ ^ 2 : ℝ)) : ℂ)‖
      ≤ ‖l₁‖ * |Real.log (‖p.1‖ ^ 2)| + ‖l₂‖ * |Real.log (‖p.2‖ ^ 2)| := by
    calc _ ≤ ‖l₁ * Complex.log (((‖p.1‖ ^ 2 : ℝ)) : ℂ)‖ + ‖l₂ * Complex.log (((‖p.2‖ ^ 2 : ℝ)) : ℂ)‖ :=
          norm_add_le _ _
      _ = _ := by rw [norm_mul, norm_mul, norm_log_ofReal_norm_sq, norm_log_ofReal_norm_sq]

  have hz : ‖zintC Ψ k₁ k₂ (l₁ * w + c₁) (l₂ * w + c₂) p‖
      = ‖Ψ p.1 p.2‖ * ‖kerC k₁ (l₁ * w + c₁) p.1‖ * ‖kerC k₂ (l₂ * w + c₂) p.2‖ := by
    rw [show zintC Ψ k₁ k₂ (l₁ * w + c₁) (l₂ * w + c₂) p
        = Ψ p.1 p.2 * kerC k₁ (l₁ * w + c₁) p.1 * kerC k₂ (l₂ * w + c₂) p.2 from rfl, norm_mul, norm_mul]

  have step1 : ‖zintDC Ψ k₁ k₂ l₁ c₁ l₂ c₂ w p‖
      ≤ ‖Ψ p.1 p.2‖ * (‖l₁‖ * ((‖kerC k₁ (l₁ * w + c₁) p.1‖ * |Real.log (‖p.1‖ ^ 2)|) * ‖kerC k₂ (l₂ * w + c₂) p.2‖)
          + ‖l₂‖ * (‖kerC k₁ (l₁ * w + c₁) p.1‖ * (‖kerC k₂ (l₂ * w + c₂) p.2‖ * |Real.log (‖p.2‖ ^ 2)|))) := by
    unfold zintDC
    rw [norm_mul, hz]
    calc ‖Ψ p.1 p.2‖ * ‖kerC k₁ (l₁ * w + c₁) p.1‖ * ‖kerC k₂ (l₂ * w + c₂) p.2‖
          * ‖l₁ * Complex.log (((‖p.1‖ ^ 2 : ℝ)) : ℂ) + l₂ * Complex.log (((‖p.2‖ ^ 2 : ℝ)) : ℂ)‖
        ≤ ‖Ψ p.1 p.2‖ * ‖kerC k₁ (l₁ * w + c₁) p.1‖ * ‖kerC k₂ (l₂ * w + c₂) p.2‖
            * (‖l₁‖ * |Real.log (‖p.1‖ ^ 2)| + ‖l₂‖ * |Real.log (‖p.2‖ ^ 2)|) :=
          mul_le_mul_of_nonneg_left hlogfac (by positivity)
      _ = _ := by ring
  have step2 : ‖l₁‖ * ((‖kerC k₁ (l₁ * w + c₁) p.1‖ * |Real.log (‖p.1‖ ^ 2)|) * ‖kerC k₂ (l₂ * w + c₂) p.2‖)
        + ‖l₂‖ * (‖kerC k₁ (l₁ * w + c₁) p.1‖ * (‖kerC k₂ (l₂ * w + c₂) p.2‖ * |Real.log (‖p.2‖ ^ 2)|))
      ≤ (‖l₁‖ + ‖l₂‖) * (bigprofC σlo σhi p.1 * bigprofC σlo σhi p.2) := by
    have e1 : (‖kerC k₁ (l₁ * w + c₁) p.1‖ * |Real.log (‖p.1‖ ^ 2)|) * ‖kerC k₂ (l₂ * w + c₂) p.2‖
        ≤ logprofC σlo σhi p.1 * profC σlo σhi p.2 := mul_le_mul hkl₁ hk₂ hn₂ hl₁
    have e2 : ‖kerC k₁ (l₁ * w + c₁) p.1‖ * (‖kerC k₂ (l₂ * w + c₂) p.2‖ * |Real.log (‖p.2‖ ^ 2)|)
        ≤ profC σlo σhi p.1 * logprofC σlo σhi p.2 := mul_le_mul hk₁ hkl₂ (by positivity) hp₁
    have e3 : logprofC σlo σhi p.1 * profC σlo σhi p.2 ≤ bigprofC σlo σhi p.1 * bigprofC σlo σhi p.2 := by
      unfold bigprofC; nlinarith [mul_nonneg hp₁ hp₂, mul_nonneg hl₁ hl₂, mul_nonneg hp₁ hl₂, mul_nonneg hl₁ hp₂]
    have e4 : profC σlo σhi p.1 * logprofC σlo σhi p.2 ≤ bigprofC σlo σhi p.1 * bigprofC σlo σhi p.2 := by
      unfold bigprofC; nlinarith [mul_nonneg hp₁ hp₂, mul_nonneg hl₁ hl₂, mul_nonneg hp₁ hl₂, mul_nonneg hl₁ hp₂]
    have f1 := mul_le_mul_of_nonneg_left (e1.trans e3) (norm_nonneg l₁)
    have f2 := mul_le_mul_of_nonneg_left (e2.trans e4) (norm_nonneg l₂)
    nlinarith [f1, f2]
  have hB₁ := bigprofC_nonneg hlo σhi p.1
  have hB₂ := bigprofC_nonneg hlo σhi p.2
  have hsq : Real.sqrt (C * (‖l₁‖ + ‖l₂‖)) * Real.sqrt (C * (‖l₁‖ + ‖l₂‖)) = C * (‖l₁‖ + ‖l₂‖) :=
    Real.mul_self_sqrt hK0
  calc ‖zintDC Ψ k₁ k₂ l₁ c₁ l₂ c₂ w p‖
      ≤ ‖Ψ p.1 p.2‖ * ((‖l₁‖ + ‖l₂‖) * (bigprofC σlo σhi p.1 * bigprofC σlo σhi p.2)) :=
        step1.trans (mul_le_mul_of_nonneg_left step2 (norm_nonneg _))
    _ ≤ (C * (Real.exp (-δ * ‖p.1‖ ^ 2) * Real.exp (-δ * ‖p.2‖ ^ 2)))
          * ((‖l₁‖ + ‖l₂‖) * (bigprofC σlo σhi p.1 * bigprofC σlo σhi p.2)) :=
        mul_le_mul_of_nonneg_right hΨ (by positivity)
    _ = Real.sqrt (C * (‖l₁‖ + ‖l₂‖)) * (bigprofC σlo σhi p.1 * Real.exp (-δ * ‖p.1‖ ^ 2))
          * (Real.sqrt (C * (‖l₁‖ + ‖l₂‖)) * (bigprofC σlo σhi p.2 * Real.exp (-δ * ‖p.2‖ ^ 2))) := by
        linear_combination (-(Real.exp (-δ * ‖p.1‖ ^ 2) * Real.exp (-δ * ‖p.2‖ ^ 2) * bigprofC σlo σhi p.1
          * bigprofC σlo σhi p.2)) * hsq

private theorem ClsC.differentiableAt_ZC_line {Ψ : ℂ → ℂ → ℂ} (h : ClsC Ψ) (k₁ k₂ : ℤ) (l₁ c₁ l₂ c₂ : ℂ) {w₀ : ℂ}
    (h₁ : 0 < (l₁ * w₀ + c₁).re) (h₂ : 0 < (l₂ * w₀ + c₂).re) :
    DifferentiableAt ℂ (fun w => ZC Ψ k₁ k₂ (l₁ * w + c₁) (l₂ * w + c₂)) w₀ := by
  set ρ : ℝ := min (l₁ * w₀ + c₁).re (l₂ * w₀ + c₂).re / 2 with hρ
  have hρ0 : 0 < ρ := by positivity
  set σhi : ℝ := max (l₁ * w₀ + c₁).re (l₂ * w₀ + c₂).re + ρ with hσhi
  have hρσ : ρ ≤ σhi := by
    have : ρ ≤ max (l₁ * w₀ + c₁).re (l₂ * w₀ + c₂).re := by
      rw [hρ]; linarith [min_le_max (a := (l₁ * w₀ + c₁).re) (b := (l₂ * w₀ + c₂).re), hρ0]
    linarith
  set r : ℝ := ρ / (‖l₁‖ + ‖l₂‖ + 1) with hr
  have hr0 : 0 < r := by positivity
  have shift : ∀ (l c : ℂ), ‖l‖ ≤ ‖l₁‖ + ‖l₂‖ + 1 → ∀ w ∈ Metric.ball w₀ r,
      |(l * w + c).re - (l * w₀ + c).re| ≤ ρ := by
    intro l c hl w hw
    have hlr : ‖l‖ * r ≤ ρ := by
      rw [hr, mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith [norm_nonneg l, hρ0, hl]
    have hd : ‖w - w₀‖ < r := by rwa [Metric.mem_ball, Complex.dist_eq] at hw
    calc |(l * w + c).re - (l * w₀ + c).re| = |(l * (w - w₀)).re| := by
          congr 1
          simp only [Complex.add_re, Complex.mul_re, Complex.sub_re, Complex.sub_im]
          ring
      _ ≤ ‖l * (w - w₀)‖ := Complex.abs_re_le_norm _
      _ = ‖l‖ * ‖w - w₀‖ := norm_mul _ _
      _ ≤ ‖l‖ * r := mul_le_mul_of_nonneg_left hd.le (norm_nonneg _)
      _ ≤ ρ := hlr
  have hrange : ∀ w ∈ Metric.ball w₀ r,
      ρ ≤ (l₁ * w + c₁).re ∧ (l₁ * w + c₁).re ≤ σhi ∧ ρ ≤ (l₂ * w + c₂).re ∧ (l₂ * w + c₂).re ≤ σhi := by
    intro w hw
    have s₁ := shift l₁ c₁ (by linarith [norm_nonneg l₂]) w hw
    have s₂ := shift l₂ c₂ (by linarith [norm_nonneg l₁]) w hw
    rw [abs_le] at s₁ s₂
    have m₁ := min_le_left (l₁ * w₀ + c₁).re (l₂ * w₀ + c₂).re
    have m₂ := min_le_right (l₁ * w₀ + c₁).re (l₂ * w₀ + c₂).re
    have M₁ := le_max_left (l₁ * w₀ + c₁).re (l₂ * w₀ + c₂).re
    have M₂ := le_max_right (l₁ * w₀ + c₁).re (l₂ * w₀ + c₂).re
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [s₁.1, s₁.2, s₂.1, s₂.2]
  obtain ⟨D, hD, hDb⟩ := h.exists_dominatorD hρ0 hρσ k₁ k₂ l₁ c₁ l₂ c₂
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (volume : Measure ℂ).prod volume)
    (F := fun w p => zintC Ψ k₁ k₂ (l₁ * w + c₁) (l₂ * w + c₂) p) (F' := zintDC Ψ k₁ k₂ l₁ c₁ l₂ c₂) (x₀ := w₀)
    (bound := fun p : ℂ × ℂ => D p.1 * D p.2) (Metric.ball_mem_nhds w₀ hr0)
    (Filter.Eventually.of_forall fun w => h.aestronglyMeasurable_zintC k₁ k₂ _ _) (h.integrable_zintC k₁ k₂ h₁ h₂)
    (h.aestronglyMeasurable_zintDC k₁ k₂ l₁ c₁ l₂ c₂ w₀)
    (ae_off_axes_C.mono fun p hp w hw => by
      obtain ⟨r₁, r₂, r₃, r₄⟩ := hrange w hw
      exact hDb w r₁ r₂ r₃ r₄ p hp.1 hp.2)
    (hD.mul_prod hD)
    (ae_off_axes_C.mono fun p hp w _ => hasDerivAt_zintC_line Ψ k₁ k₂ l₁ c₁ l₂ c₂ hp.1 hp.2 w)
  exact key.2.differentiableAt

private theorem ClsC.differentiableOn_ZC_line {Ψ : ℂ → ℂ → ℂ} (h : ClsC Ψ) (k₁ k₂ : ℤ) (l₁ c₁ l₂ c₂ : ℂ) :
    DifferentiableOn ℂ (fun w => ZC Ψ k₁ k₂ (l₁ * w + c₁) (l₂ * w + c₂))
      {w : ℂ | 0 < (l₁ * w + c₁).re ∧ 0 < (l₂ * w + c₂).re} :=
  fun _ hw => (h.differentiableAt_ZC_line k₁ k₂ l₁ c₁ l₂ c₂ hw.1 hw.2).differentiableWithinAt

end W3C

end TateComplex

end

end

section

noncomputable section

open Complex MeasureTheory Set LanglandsTunnell.TateLocal LanglandsTunnell.ArchPlace
open scoped Topology

namespace TateComplex

namespace W3C

private theorem Gammaℂ_ne_zero_of_re_pos {s : ℂ} (hs : 0 < s.re) : Gammaℂ s ≠ 0 := by
  rw [← Gammaℝ_mul_Gammaℝ_add_one]
  refine mul_ne_zero (Gammaℝ_ne_zero_of_re_pos hs) (Gammaℝ_ne_zero_of_re_pos ?_)
  rw [Complex.add_re, Complex.one_re]
  linarith

private theorem differentiable_Gammaℂ_inv : Differentiable ℂ fun s : ℂ => (Gammaℂ s)⁻¹ := by
  have e : (fun s : ℂ => (Gammaℂ s)⁻¹) = fun s => (Gammaℝ s)⁻¹ * (Gammaℝ (s + 1))⁻¹ := by
    funext s
    rw [← Gammaℝ_mul_Gammaℝ_add_one, mul_inv]
  rw [e]
  intro s
  exact (differentiable_Gammaℝ_inv s).mul ((differentiable_Gammaℝ_inv _).comp s (by fun_prop))

private theorem re_add_half_natAbs (w : ℂ) (k : ℤ) : (w + (k.natAbs : ℂ) / 2).re = w.re + (k.natAbs : ℝ) / 2 := by
  rw [Complex.add_re, Complex.div_ofNat_re, Complex.natCast_re]

private theorem Gammaℂ_shift_ne_zero {w : ℂ} (hw : 0 < w.re) (k : ℤ) : Gammaℂ (w + (k.natAbs : ℂ) / 2) ≠ 0 :=
  Gammaℂ_ne_zero_of_re_pos (by rw [re_add_half_natAbs]; positivity)

private theorem cC_ne_zero (k : ℤ) : cC k ≠ 0 := by
  unfold cC
  exact div_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr I_ne_zero)) two_ne_zero

private def EchartC (Ψ : ℂ → ℂ → ℂ) (k₁ k₂ : ℤ) (w₁ w₂ : ℂ) : ℂ :=
  ZC Ψ k₁ k₂ w₁ w₂ * (Gammaℂ (w₁ + (k₁.natAbs : ℂ) / 2))⁻¹ * (Gammaℂ (w₂ + (k₂.natAbs : ℂ) / 2))⁻¹

private theorem ClsC.differentiableAt_EchartC_line {Ψ : ℂ → ℂ → ℂ} (h : ClsC Ψ) (k₁ k₂ : ℤ) (l₁ c₁ l₂ c₂ : ℂ)
    {w₀ : ℂ} (h₁ : 0 < (l₁ * w₀ + c₁).re) (h₂ : 0 < (l₂ * w₀ + c₂).re) :
    DifferentiableAt ℂ (fun w => EchartC Ψ k₁ k₂ (l₁ * w + c₁) (l₂ * w + c₂)) w₀ := by
  unfold EchartC
  have g₁ : DifferentiableAt ℂ (fun w => (Gammaℂ (l₁ * w + c₁ + (k₁.natAbs : ℂ) / 2))⁻¹) w₀ :=
    (differentiable_Gammaℂ_inv _).comp w₀ (by fun_prop)
  have g₂ : DifferentiableAt ℂ (fun w => (Gammaℂ (l₂ * w + c₂ + (k₂.natAbs : ℂ) / 2))⁻¹) w₀ :=
    (differentiable_Gammaℂ_inv _).comp w₀ (by fun_prop)
  exact ((h.differentiableAt_ZC_line k₁ k₂ l₁ c₁ l₂ c₂ h₁ h₂).mul g₁).mul g₂

private theorem ClsC.EchartC_F₁C {Ψ : ℂ → ℂ → ℂ} (h : ClsC Ψ) (k₁ k₂ : ℤ) {w₁ w₂ : ℂ} (h0 : 0 < w₁.re) (h1 : w₁.re < 1)
    (h2 : 0 < w₂.re) : EchartC (W3C.F₁C Ψ) k₁ k₂ (1 - w₁) w₂ = cC k₁ * EchartC Ψ k₁ k₂ w₁ w₂ := by
  have hZ := h.ZC_F₁C k₁ k₂ h0 h1 h2
  have hg₁ := Gammaℂ_shift_ne_zero h0 k₁
  have hg₁' : Gammaℂ (1 - w₁ + (k₁.natAbs : ℂ) / 2) ≠ 0 :=
    Gammaℂ_shift_ne_zero (by simp only [Complex.sub_re, Complex.one_re]; linarith) k₁
  unfold EchartC
  rw [(eq_mul_inv_iff_mul_eq₀ hg₁).mpr hZ]
  linear_combination (cC k₁ * ZC Ψ k₁ k₂ w₁ w₂ * (Gammaℂ (w₁ + (k₁.natAbs : ℂ) / 2))⁻¹
    * (Gammaℂ (w₂ + (k₂.natAbs : ℂ) / 2))⁻¹) * mul_inv_cancel₀ hg₁'

private theorem ClsC.EchartC_F₂C {Ψ : ℂ → ℂ → ℂ} (h : ClsC Ψ) (k₁ k₂ : ℤ) {w₁ w₂ : ℂ} (h1 : 0 < w₁.re) (h0 : 0 < w₂.re)
    (h2 : w₂.re < 1) : EchartC (W3C.F₂C Ψ) k₁ k₂ w₁ (1 - w₂) = cC k₂ * EchartC Ψ k₁ k₂ w₁ w₂ := by
  have hZ := h.ZC_F₂C k₁ k₂ h1 h0 h2
  have hg₂ := Gammaℂ_shift_ne_zero h0 k₂
  have hg₂' : Gammaℂ (1 - w₂ + (k₂.natAbs : ℂ) / 2) ≠ 0 :=
    Gammaℂ_shift_ne_zero (by simp only [Complex.sub_re, Complex.one_re]; linarith) k₂
  unfold EchartC
  rw [(eq_mul_inv_iff_mul_eq₀ hg₂).mpr hZ]
  linear_combination (cC k₂ * ZC Ψ k₁ k₂ w₁ w₂ * (Gammaℂ (w₁ + (k₁.natAbs : ℂ) / 2))⁻¹
    * (Gammaℂ (w₂ + (k₂.natAbs : ℂ) / 2))⁻¹) * mul_inv_cancel₀ hg₂'

private def E₁C (Ψ : ℂ → ℂ → ℂ) (k₁ k₂ : ℤ) (w₁ w₂ : ℂ) : ℂ :=
  if 0 < w₁.re then EchartC Ψ k₁ k₂ w₁ w₂ else (cC k₁)⁻¹ * EchartC (W3C.F₁C Ψ) k₁ k₂ (1 - w₁) w₂

private theorem E₁C_of_re_pos (Ψ : ℂ → ℂ → ℂ) (k₁ k₂ : ℤ) {w₁ : ℂ} (h1 : 0 < w₁.re) (w₂ : ℂ) :
    E₁C Ψ k₁ k₂ w₁ w₂ = EchartC Ψ k₁ k₂ w₁ w₂ := if_pos h1

private theorem ClsC.E₁C_of_re_lt_one {Ψ : ℂ → ℂ → ℂ} (h : ClsC Ψ) (k₁ k₂ : ℤ) {w₁ w₂ : ℂ} (h1 : w₁.re < 1)
    (h2 : 0 < w₂.re) : E₁C Ψ k₁ k₂ w₁ w₂ = (cC k₁)⁻¹ * EchartC (W3C.F₁C Ψ) k₁ k₂ (1 - w₁) w₂ := by
  unfold E₁C
  split_ifs with h0
  · rw [h.EchartC_F₁C k₁ k₂ h0 h1 h2, ← mul_assoc, inv_mul_cancel₀ (cC_ne_zero k₁), one_mul]
  · rfl

private theorem ClsC.differentiableAt_E₁C_line {Ψ : ℂ → ℂ → ℂ} (h : ClsC Ψ) (k₁ k₂ : ℤ) (l₁ c₁ l₂ c₂ : ℂ) {w₀ : ℂ}
    (h₂ : 0 < (l₂ * w₀ + c₂).re) :
    DifferentiableAt ℂ (fun w => E₁C Ψ k₁ k₂ (l₁ * w + c₁) (l₂ * w + c₂)) w₀ := by
  have cont₁ : Continuous fun w : ℂ => (l₁ * w + c₁).re := by fun_prop
  have cont₂ : Continuous fun w : ℂ => (l₂ * w + c₂).re := by fun_prop
  have ev₂ : ∀ᶠ w in 𝓝 w₀, 0 < (l₂ * w + c₂).re :=
    (continuousAt_const).eventually_lt cont₂.continuousAt h₂
  by_cases h₁ : 0 < (l₁ * w₀ + c₁).re
  · have ev₁ : ∀ᶠ w in 𝓝 w₀, 0 < (l₁ * w + c₁).re := (continuousAt_const).eventually_lt cont₁.continuousAt h₁
    refine (h.differentiableAt_EchartC_line k₁ k₂ l₁ c₁ l₂ c₂ h₁ h₂).congr_of_eventuallyEq ?_
    exact ev₁.mono fun w hw => E₁C_of_re_pos Ψ k₁ k₂ hw _
  · have h₁' : (l₁ * w₀ + c₁).re < 1 := by have := not_lt.mp h₁; linarith
    have ev₁ : ∀ᶠ w in 𝓝 w₀, (l₁ * w + c₁).re < 1 := cont₁.continuousAt.eventually_lt continuousAt_const h₁'
    have hd : DifferentiableAt ℂ
        (fun w => (cC k₁)⁻¹ * EchartC (W3C.F₁C Ψ) k₁ k₂ (-l₁ * w + (1 - c₁)) (l₂ * w + c₂)) w₀ := by
      refine (h.F₁C.differentiableAt_EchartC_line k₁ k₂ (-l₁) (1 - c₁) l₂ c₂ ?_ h₂).const_mul _
      have e : -l₁ * w₀ + (1 - c₁) = 1 - (l₁ * w₀ + c₁) := by ring
      rw [e, Complex.sub_re, Complex.one_re]; linarith
    refine hd.congr_of_eventuallyEq ?_
    refine (ev₁.and ev₂).mono fun w ⟨hw₁, hw₂⟩ => ?_
    beta_reduce
    rw [h.E₁C_of_re_lt_one k₁ k₂ hw₁ hw₂]
    congr 2
    ring

private theorem ClsC.E₁C_F₂C {Ψ : ℂ → ℂ → ℂ} (h : ClsC Ψ) (k₁ k₂ : ℤ) {w₂ : ℂ} (h0 : 0 < w₂.re) (h2 : w₂.re < 1)
    (w₁ : ℂ) : E₁C (W3C.F₂C Ψ) k₁ k₂ w₁ (1 - w₂) = cC k₂ * E₁C Ψ k₁ k₂ w₁ w₂ := by
  have h1w : 0 < (1 - w₂).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
  have df : Differentiable ℂ fun w₁ => E₁C (W3C.F₂C Ψ) k₁ k₂ w₁ (1 - w₂) := fun w => by
    have := h.F₂C.differentiableAt_E₁C_line k₁ k₂ 1 0 0 (1 - w₂) (w₀ := w) (by simpa using h1w)
    simpa using this
  have dg : Differentiable ℂ fun w₁ => cC k₂ * E₁C Ψ k₁ k₂ w₁ w₂ := fun w => by
    have := h.differentiableAt_E₁C_line k₁ k₂ 1 0 0 w₂ (w₀ := w) (by simpa using h0)
    simpa using this.const_mul (cC k₂)
  have e := TateReal.W3.entire_eq_of_eqOn_open df dg TateReal.W3.isOpen_re_pos (z₀ := 1) (by simp)
    fun z hz => by
      simp only [Set.mem_setOf_eq] at hz
      rw [E₁C_of_re_pos _ k₁ k₂ hz, E₁C_of_re_pos _ k₁ k₂ hz, h.EchartC_F₂C k₁ k₂ hz h0 h2]
  exact congrFun e w₁

private def EC (Ψ : ℂ → ℂ → ℂ) (k₁ k₂ : ℤ) (w₁ w₂ : ℂ) : ℂ :=
  if 0 < w₂.re then E₁C Ψ k₁ k₂ w₁ w₂ else (cC k₂)⁻¹ * E₁C (W3C.F₂C Ψ) k₁ k₂ w₁ (1 - w₂)

private theorem EC_of_re_pos (Ψ : ℂ → ℂ → ℂ) (k₁ k₂ : ℤ) (w₁ : ℂ) {w₂ : ℂ} (h2 : 0 < w₂.re) :
    EC Ψ k₁ k₂ w₁ w₂ = E₁C Ψ k₁ k₂ w₁ w₂ := if_pos h2

private theorem ClsC.EC_of_re_lt_one {Ψ : ℂ → ℂ → ℂ} (h : ClsC Ψ) (k₁ k₂ : ℤ) (w₁ : ℂ) {w₂ : ℂ} (h2 : w₂.re < 1) :
    EC Ψ k₁ k₂ w₁ w₂ = (cC k₂)⁻¹ * E₁C (W3C.F₂C Ψ) k₁ k₂ w₁ (1 - w₂) := by
  unfold EC
  split_ifs with h0
  · rw [h.E₁C_F₂C k₁ k₂ h0 h2 w₁, ← mul_assoc, inv_mul_cancel₀ (cC_ne_zero k₂), one_mul]
  · rfl

private theorem ZC_eq_EC (Ψ : ℂ → ℂ → ℂ) (k₁ k₂ : ℤ) {w₁ w₂ : ℂ} (h₁ : 0 < w₁.re) (h₂ : 0 < w₂.re) :
    ZC Ψ k₁ k₂ w₁ w₂
      = Gammaℂ (w₁ + (k₁.natAbs : ℂ) / 2) * Gammaℂ (w₂ + (k₂.natAbs : ℂ) / 2) * EC Ψ k₁ k₂ w₁ w₂ := by
  rw [EC_of_re_pos _ _ _ _ h₂, E₁C_of_re_pos _ _ _ h₁]
  unfold EchartC
  linear_combination (-(ZC Ψ k₁ k₂ w₁ w₂) * Gammaℂ (w₂ + (k₂.natAbs : ℂ) / 2)
      * (Gammaℂ (w₂ + (k₂.natAbs : ℂ) / 2))⁻¹) * mul_inv_cancel₀ (Gammaℂ_shift_ne_zero h₁ k₁)
    + (-(ZC Ψ k₁ k₂ w₁ w₂)) * mul_inv_cancel₀ (Gammaℂ_shift_ne_zero h₂ k₂)

private theorem ClsC.differentiable_EC_line {Ψ : ℂ → ℂ → ℂ} (h : ClsC Ψ) (k₁ k₂ : ℤ) (l₁ c₁ l₂ c₂ : ℂ) :
    Differentiable ℂ fun w => EC Ψ k₁ k₂ (l₁ * w + c₁) (l₂ * w + c₂) := by
  intro w₀
  have cont₂ : Continuous fun w : ℂ => (l₂ * w + c₂).re := by fun_prop
  by_cases h₂ : 0 < (l₂ * w₀ + c₂).re
  · have ev₂ : ∀ᶠ w in 𝓝 w₀, 0 < (l₂ * w + c₂).re := (continuousAt_const).eventually_lt cont₂.continuousAt h₂
    refine (h.differentiableAt_E₁C_line k₁ k₂ l₁ c₁ l₂ c₂ h₂).congr_of_eventuallyEq ?_
    exact ev₂.mono fun w hw => EC_of_re_pos Ψ k₁ k₂ _ hw
  · have h₂' : (l₂ * w₀ + c₂).re < 1 := by have := not_lt.mp h₂; linarith
    have ev₂ : ∀ᶠ w in 𝓝 w₀, (l₂ * w + c₂).re < 1 := cont₂.continuousAt.eventually_lt continuousAt_const h₂'
    have hd : DifferentiableAt ℂ
        (fun w => (cC k₂)⁻¹ * E₁C (W3C.F₂C Ψ) k₁ k₂ (l₁ * w + c₁) (-l₂ * w + (1 - c₂))) w₀ := by
      refine (h.F₂C.differentiableAt_E₁C_line k₁ k₂ l₁ c₁ (-l₂) (1 - c₂) ?_).const_mul _
      have e : -l₂ * w₀ + (1 - c₂) = 1 - (l₂ * w₀ + c₂) := by ring
      rw [e, Complex.sub_re, Complex.one_re]; linarith
    refine hd.congr_of_eventuallyEq ?_
    refine ev₂.mono fun w hw => ?_
    beta_reduce
    rw [h.EC_of_re_lt_one k₁ k₂ _ hw]
    congr 2
    ring

private theorem ClsC.differentiable_EC_comp {Ψ : ℂ → ℂ → ℂ} (h : ClsC Ψ) (k₁ k₂ : ℤ) {f₁ f₂ : ℂ → ℂ} (l₁ c₁ l₂ c₂ : ℂ)
    (e₁ : ∀ w, f₁ w = l₁ * w + c₁) (e₂ : ∀ w, f₂ w = l₂ * w + c₂) :
    Differentiable ℂ fun w => EC Ψ k₁ k₂ (f₁ w) (f₂ w) := by
  have e : (fun w => EC Ψ k₁ k₂ (f₁ w) (f₂ w)) = fun w => EC Ψ k₁ k₂ (l₁ * w + c₁) (l₂ * w + c₂) :=
    funext fun w => by rw [e₁, e₂]
  rw [e]
  exact h.differentiable_EC_line k₁ k₂ l₁ c₁ l₂ c₂

private theorem ClsC.differentiable_EC_fst {Ψ : ℂ → ℂ → ℂ} (h : ClsC Ψ) (k₁ k₂ : ℤ) (w₂ : ℂ) :
    Differentiable ℂ fun w₁ => EC Ψ k₁ k₂ w₁ w₂ :=
  h.differentiable_EC_comp k₁ k₂ 1 0 0 w₂ (fun w => by ring) (fun w => by ring)

private theorem ClsC.differentiable_EC_snd {Ψ : ℂ → ℂ → ℂ} (h : ClsC Ψ) (k₁ k₂ : ℤ) (w₁ : ℂ) :
    Differentiable ℂ fun w₂ => EC Ψ k₁ k₂ w₁ w₂ :=
  h.differentiable_EC_comp k₁ k₂ 0 w₁ 1 0 (fun w => by ring) (fun w => by ring)

private theorem ext_EC {f g : ℂ → ℂ → ℂ}
    (hf₁ : ∀ w₂, Differentiable ℂ fun w₁ => f w₁ w₂) (hg₁ : ∀ w₂, Differentiable ℂ fun w₁ => g w₁ w₂)
    (hf₂ : ∀ w₁, Differentiable ℂ fun w₂ => f w₁ w₂) (hg₂ : ∀ w₁, Differentiable ℂ fun w₂ => g w₁ w₂)
    (h : ∀ w₁ w₂, 0 < w₁.re → 0 < w₂.re → f w₁ w₂ = g w₁ w₂) : ∀ w₁ w₂, f w₁ w₂ = g w₁ w₂ :=
  TateReal.W3.ext_of_eqOn_rect hf₁ hg₁ hf₂ hg₂ TateReal.W3.isOpen_re_pos TateReal.W3.isOpen_re_pos (z₁ := 1)
    (z₂ := 1) (by simp) (by simp) fun w₁ h₁ w₂ h₂ => h w₁ w₂ h₁ h₂

private theorem ClsC.EC_F₁C {Ψ : ℂ → ℂ → ℂ} (h : ClsC Ψ) (k₁ k₂ : ℤ) (w₁ w₂ : ℂ) :
    EC (W3C.F₁C Ψ) k₁ k₂ (1 - w₁) w₂ = cC k₁ * EC Ψ k₁ k₂ w₁ w₂ := by
  refine TateReal.W3.ext_of_eqOn_rect (f := fun w₁ w₂ => EC (W3C.F₁C Ψ) k₁ k₂ (1 - w₁) w₂)
    (g := fun w₁ w₂ => cC k₁ * EC Ψ k₁ k₂ w₁ w₂)
    (fun w₂ => h.F₁C.differentiable_EC_comp k₁ k₂ (-1) 1 0 w₂ (fun w => by ring) (fun w => by ring))
    (fun w₂ => (h.differentiable_EC_fst k₁ k₂ w₂).const_mul _)
    (fun w₁ => h.F₁C.differentiable_EC_comp k₁ k₂ 0 (1 - w₁) 1 0 (fun w => by ring) (fun w => by ring))
    (fun w₁ => (h.differentiable_EC_snd k₁ k₂ w₁).const_mul _)
    TateReal.W3.isOpen_re_lt_one TateReal.W3.isOpen_re_pos (z₁ := 0) (z₂ := 1) (by simp) (by simp) ?_ w₁ w₂
  intro u₁ hu₁ u₂ hu₂
  simp only [Set.mem_setOf_eq] at hu₁ hu₂
  have h1u : 0 < (1 - u₁).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
  try simp only
  rw [EC_of_re_pos _ _ _ _ hu₂, E₁C_of_re_pos _ _ _ h1u, EC_of_re_pos _ _ _ _ hu₂, h.E₁C_of_re_lt_one k₁ k₂ hu₁ hu₂,
    ← mul_assoc, mul_inv_cancel₀ (cC_ne_zero k₁), one_mul]

private theorem ClsC.EC_F₂C {Ψ : ℂ → ℂ → ℂ} (h : ClsC Ψ) (k₁ k₂ : ℤ) (w₁ w₂ : ℂ) :
    EC (W3C.F₂C Ψ) k₁ k₂ w₁ (1 - w₂) = cC k₂ * EC Ψ k₁ k₂ w₁ w₂ := by
  have df : Differentiable ℂ fun w₂ => EC (W3C.F₂C Ψ) k₁ k₂ w₁ (1 - w₂) :=
    h.F₂C.differentiable_EC_comp k₁ k₂ 0 w₁ (-1) 1 (fun w => by ring) (fun w => by ring)
  have dg : Differentiable ℂ fun w₂ => cC k₂ * EC Ψ k₁ k₂ w₁ w₂ := (h.differentiable_EC_snd k₁ k₂ w₁).const_mul _
  have e := TateReal.W3.entire_eq_of_eqOn_open df dg TateReal.W3.isOpen_re_lt_one (z₀ := 0) (by simp)
    fun u hu => by
      simp only [Set.mem_setOf_eq] at hu
      have h1u : 0 < (1 - u).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
      rw [EC_of_re_pos _ _ _ _ h1u, h.EC_of_re_lt_one k₁ k₂ w₁ hu, ← mul_assoc, mul_inv_cancel₀ (cC_ne_zero k₂),
        one_mul]
  exact congrFun e w₂

private theorem ClsC.EC_swap {Ψ : ℂ → ℂ → ℂ} (h : ClsC Ψ) (k₁ k₂ : ℤ) (w₁ w₂ : ℂ) :
    EC (fun z t => Ψ t z) k₂ k₁ w₂ w₁ = EC Ψ k₁ k₂ w₁ w₂ := by
  refine ext_EC (f := fun w₁ w₂ => EC (fun z t => Ψ t z) k₂ k₁ w₂ w₁) (g := fun w₁ w₂ => EC Ψ k₁ k₂ w₁ w₂)
    (fun w₂ => h.swap.differentiable_EC_snd k₂ k₁ w₂) (fun w₂ => h.differentiable_EC_fst k₁ k₂ w₂)
    (fun w₁ => h.swap.differentiable_EC_fst k₂ k₁ w₁) (fun w₁ => h.differentiable_EC_snd k₁ k₂ w₁) ?_ w₁ w₂
  intro u₁ u₂ h₁ h₂
  try simp only
  rw [EC_of_re_pos _ _ _ _ h₁, E₁C_of_re_pos _ _ _ h₂, EC_of_re_pos _ _ _ _ h₂, E₁C_of_re_pos _ _ _ h₁]
  unfold EchartC
  rw [ZC_swap]
  ring

private theorem ClsC.EC_smul {Ψ : ℂ → ℂ → ℂ} (h : ClsC Ψ) (c : ℂ) (k₁ k₂ : ℤ) (w₁ w₂ : ℂ) :
    EC (fun z t => c * Ψ z t) k₁ k₂ w₁ w₂ = c * EC Ψ k₁ k₂ w₁ w₂ := by
  refine ext_EC (f := fun w₁ w₂ => EC (fun z t => c * Ψ z t) k₁ k₂ w₁ w₂) (g := fun w₁ w₂ => c * EC Ψ k₁ k₂ w₁ w₂)
    (fun w₂ => (h.smul c).differentiable_EC_fst k₁ k₂ w₂) (fun w₂ => (h.differentiable_EC_fst k₁ k₂ w₂).const_mul _)
    (fun w₁ => (h.smul c).differentiable_EC_snd k₁ k₂ w₁) (fun w₁ => (h.differentiable_EC_snd k₁ k₂ w₁).const_mul _)
    ?_ w₁ w₂
  intro u₁ u₂ h₁ h₂
  try simp only
  rw [EC_of_re_pos _ _ _ _ h₂, E₁C_of_re_pos _ _ _ h₁, EC_of_re_pos _ _ _ _ h₂, E₁C_of_re_pos _ _ _ h₁]
  unfold EchartC
  rw [ZC_smul]
  ring

end W3C

end TateComplex

end

end

section

noncomputable section

open Complex MeasureTheory Set LanglandsTunnell.TateLocal LanglandsTunnell.ArchPlace

namespace TateComplex

namespace W3C

private theorem im_add_half_natAbs (w : ℂ) (k : ℤ) : (w + (k.natAbs : ℂ) / 2).im = w.im := by
  rw [Complex.add_im, Complex.div_ofNat_im, Complex.natCast_im, zero_div, add_zero]

private theorem norm_cC (k : ℤ) : ‖cC k‖ = 1 / 2 := by
  unfold cC
  rw [norm_div, norm_pow, norm_neg, Complex.norm_I, one_pow, Complex.norm_ofNat]

private theorem norm_cC_inv_mul (k : ℤ) (z : ℂ) : ‖(cC k)⁻¹ * z‖ = 2 * ‖z‖ := by
  rw [norm_mul, norm_inv, norm_cC]
  norm_num

private theorem exists_bound_invGammaℂ_strip' (A B : ℝ) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ w : ℂ, A ≤ w.re → w.re ≤ B → ‖(Gammaℂ w)⁻¹‖ ≤ C * Real.exp (D * |w.im|) := by
  obtain ⟨C, D, hC, hD, hCD⟩ := TateReal.W3.exists_bound_invGammaℝ_strip' A (B + 1)
  refine ⟨C * C, 2 * D, by positivity, by positivity, fun w h1 h2 => ?_⟩
  have g₁ := hCD w h1 (by linarith)
  have g₂ := hCD (w + 1) (by rw [Complex.add_re, Complex.one_re]; linarith)
    (by rw [Complex.add_re, Complex.one_re]; linarith)
  rw [Complex.add_im, Complex.one_im, add_zero] at g₂
  rw [← Gammaℝ_mul_Gammaℝ_add_one, mul_inv, norm_mul]
  calc ‖(Gammaℝ w)⁻¹‖ * ‖(Gammaℝ (w + 1))⁻¹‖
      ≤ (C * Real.exp (D * |w.im|)) * (C * Real.exp (D * |w.im|)) := mul_le_mul g₁ g₂ (norm_nonneg _) (by positivity)
    _ = C * C * Real.exp (2 * D * |w.im|) := by
        rw [show 2 * D * |w.im| = D * |w.im| + D * |w.im| by ring, Real.exp_add]; ring

private theorem ClsC.exists_EchartC_bound {Ψ : ℂ → ℂ → ℂ} (h : ClsC Ψ) (k₁ k₂ : ℤ) {R : ℝ} (hR : 1 / 2 ≤ R) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ (v₁ v₂ : ℂ), 1 / 2 ≤ v₁.re → v₁.re ≤ R → 1 / 2 ≤ v₂.re → v₂.re ≤ R →
      ‖EchartC Ψ k₁ k₂ v₁ v₂‖ ≤ A * Real.exp (B * (|v₁.im| + |v₂.im|)) := by
  obtain ⟨M, hM⟩ := h.exists_ZC_bound (σlo := 1 / 2) (σhi := R) (by norm_num) (by linarith)
  obtain ⟨C, D, hC, hD, hCD⟩ :=
    exists_bound_invGammaℂ_strip' (1 / 2) (R + ((k₁.natAbs : ℝ) + (k₂.natAbs : ℝ)) / 2)
  refine ⟨|M| * C * C, D, by positivity, hD, fun v₁ v₂ h1 h2 h3 h4 => ?_⟩
  have n₁ : (0 : ℝ) ≤ k₁.natAbs := Nat.cast_nonneg _
  have n₂ : (0 : ℝ) ≤ k₂.natAbs := Nat.cast_nonneg _
  have g₁ := hCD (v₁ + (k₁.natAbs : ℂ) / 2) (by rw [re_add_half_natAbs]; linarith)
    (by rw [re_add_half_natAbs]; linarith)
  have g₂ := hCD (v₂ + (k₂.natAbs : ℂ) / 2) (by rw [re_add_half_natAbs]; linarith)
    (by rw [re_add_half_natAbs]; linarith)
  rw [im_add_half_natAbs] at g₁ g₂
  have hZ : ‖ZC Ψ k₁ k₂ v₁ v₂‖ ≤ |M| := (hM k₁ k₂ v₁ v₂ h1 h2 h3 h4).trans (le_abs_self M)
  unfold EchartC
  rw [norm_mul, norm_mul]
  calc ‖ZC Ψ k₁ k₂ v₁ v₂‖ * ‖(Gammaℂ (v₁ + (k₁.natAbs : ℂ) / 2))⁻¹‖ * ‖(Gammaℂ (v₂ + (k₂.natAbs : ℂ) / 2))⁻¹‖
      ≤ |M| * (C * Real.exp (D * |v₁.im|)) * (C * Real.exp (D * |v₂.im|)) := by
        gcongr
    _ = |M| * C * C * Real.exp (D * (|v₁.im| + |v₂.im|)) := by
        rw [mul_add, Real.exp_add]; ring

private theorem ClsC.exists_EC_strip_bound {Ψ : ℂ → ℂ → ℂ} (h : ClsC Ψ) (k₁ k₂ : ℤ) (c₁ c₂ : ℂ) (σ₁ σ₂ : ℝ) :
    ∃ A B : ℝ, ∀ w : ℂ, σ₁ ≤ w.re → w.re ≤ σ₂ →
      ‖EC Ψ k₁ k₂ (w + c₁) (w + c₂)‖ ≤ A * Real.exp (B * |w.im|) := by

  set R : ℝ := |σ₁| + |σ₂| + ‖c₁‖ + ‖c₂‖ + 2 with hR
  have hR' : 1 / 2 ≤ R := by
    have := norm_nonneg c₁; have := norm_nonneg c₂; have := abs_nonneg σ₁; have := abs_nonneg σ₂
    rw [hR]; linarith
  obtain ⟨A₁, B₁, hA₁, hB₁, b₁⟩ := h.exists_EchartC_bound k₁ k₂ hR'
  obtain ⟨A₂, B₂, hA₂, hB₂, b₂⟩ := h.F₁C.exists_EchartC_bound k₁ k₂ hR'
  obtain ⟨A₃, B₃, hA₃, hB₃, b₃⟩ := h.F₂C.exists_EchartC_bound k₁ k₂ hR'
  obtain ⟨A₄, B₄, hA₄, hB₄, b₄⟩ := h.F₂C.F₁C.exists_EchartC_bound k₁ k₂ hR'
  set A' : ℝ := A₁ + A₂ + A₃ + A₄ with hA'
  set B₀ : ℝ := B₁ + B₂ + B₃ + B₄ with hB₀
  have hA'0 : 0 ≤ A' := by rw [hA']; linarith
  have hB₀0 : 0 ≤ B₀ := by rw [hB₀]; linarith

  have fin : ∀ (c X Aᵢ Bᵢ S : ℝ), 0 ≤ c → c ≤ 4 → 0 ≤ X → 0 ≤ Aᵢ → Aᵢ ≤ A' → Bᵢ ≤ B₀ → 0 ≤ S →
      X ≤ Aᵢ * Real.exp (Bᵢ * S) → c * X ≤ 4 * A' * Real.exp (B₀ * S) := by
    intro c X Aᵢ Bᵢ S hc hc4 hX hAi hA hB hS hXle
    have e1 : Aᵢ * Real.exp (Bᵢ * S) ≤ A' * Real.exp (B₀ * S) :=
      mul_le_mul hA (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hB hS)) (Real.exp_pos _).le hA'0
    calc c * X ≤ 4 * X := mul_le_mul_of_nonneg_right hc4 hX
      _ ≤ 4 * (A' * Real.exp (B₀ * S)) := mul_le_mul_of_nonneg_left (hXle.trans e1) (by norm_num)
      _ = 4 * A' * Real.exp (B₀ * S) := by ring
  refine ⟨4 * A' * Real.exp (B₀ * (‖c₁‖ + ‖c₂‖)), 2 * B₀, fun w hw₁ hw₂ => ?_⟩

  set u₁ : ℂ := w + c₁ with hu₁
  set u₂ : ℂ := w + c₂ with hu₂
  have rc₁ := Complex.abs_re_le_norm c₁
  have rc₂ := Complex.abs_re_le_norm c₂
  have ic₁ := Complex.abs_im_le_norm c₁
  have ic₂ := Complex.abs_im_le_norm c₂
  have ru₁ : u₁.re = w.re + c₁.re := by rw [hu₁, Complex.add_re]
  have ru₂ : u₂.re = w.re + c₂.re := by rw [hu₂, Complex.add_re]
  have iu₁ : |u₁.im| ≤ |w.im| + ‖c₁‖ := by
    rw [hu₁, Complex.add_im]; exact (abs_add_le _ _).trans (by linarith)
  have iu₂ : |u₂.im| ≤ |w.im| + ‖c₂‖ := by
    rw [hu₂, Complex.add_im]; exact (abs_add_le _ _).trans (by linarith)
  have hσ₁ := le_abs_self σ₁
  have hσ₁' := neg_abs_le σ₁
  have hσ₂ := le_abs_self σ₂
  have rc₁' := (abs_le.mp rc₁)
  have rc₂' := (abs_le.mp rc₂)
  have up₁ : u₁.re ≤ R := by rw [ru₁, hR]; linarith [rc₁'.2, norm_nonneg c₂, abs_nonneg σ₁, hw₂, hσ₂]
  have up₂ : u₂.re ≤ R := by rw [ru₂, hR]; linarith [rc₂'.2, norm_nonneg c₁, abs_nonneg σ₁, hw₂, hσ₂]
  have up₁' : (1 - u₁).re ≤ R := by
    rw [Complex.sub_re, Complex.one_re, ru₁, hR]; linarith [rc₁'.1, norm_nonneg c₂, abs_nonneg σ₂, hw₁, hσ₁']
  have up₂' : (1 - u₂).re ≤ R := by
    rw [Complex.sub_re, Complex.one_re, ru₂, hR]; linarith [rc₂'.1, norm_nonneg c₁, abs_nonneg σ₂, hw₁, hσ₁']
  have im₁' : |(1 - u₁).im| = |u₁.im| := by rw [Complex.sub_im, Complex.one_im, zero_sub, abs_neg]
  have im₂' : |(1 - u₂).im| = |u₂.im| := by rw [Complex.sub_im, Complex.one_im, zero_sub, abs_neg]

  have tail : 4 * A' * Real.exp (B₀ * (|u₁.im| + |u₂.im|))
      ≤ 4 * A' * Real.exp (B₀ * (‖c₁‖ + ‖c₂‖)) * Real.exp (2 * B₀ * |w.im|) := by
    rw [mul_assoc (4 * A'), ← Real.exp_add]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left (add_le_add iu₁ iu₂) hB₀0]
  refine le_trans ?_ tail
  have S0 : 0 ≤ |u₁.im| + |u₂.im| := by positivity
  have wA₁ : A₁ ≤ A' := by rw [hA']; linarith
  have wA₂ : A₂ ≤ A' := by rw [hA']; linarith
  have wA₃ : A₃ ≤ A' := by rw [hA']; linarith
  have wA₄ : A₄ ≤ A' := by rw [hA']; linarith
  have wB₁ : B₁ ≤ B₀ := by rw [hB₀]; linarith
  have wB₂ : B₂ ≤ B₀ := by rw [hB₀]; linarith
  have wB₃ : B₃ ≤ B₀ := by rw [hB₀]; linarith
  have wB₄ : B₄ ≤ B₀ := by rw [hB₀]; linarith

  rcases le_or_gt (1 / 2) u₂.re with c2 | c2
  ·
    have p₂ : 0 < u₂.re := by linarith
    rw [EC_of_re_pos _ _ _ _ p₂]
    rcases le_or_gt (1 / 2) u₁.re with c1 | c1
    · have p₁ : 0 < u₁.re := by linarith
      rw [E₁C_of_re_pos _ _ _ p₁]
      have := fin 1 _ A₁ B₁ _ (by norm_num) (by norm_num) (norm_nonneg _) hA₁ wA₁ wB₁ S0 (b₁ u₁ u₂ c1 up₁ c2 up₂)
      rwa [one_mul] at this
    · have l₁ : u₁.re < 1 := by linarith
      have r₁ : 1 / 2 ≤ (1 - u₁).re := by rw [Complex.sub_re, Complex.one_re]; linarith
      rw [h.E₁C_of_re_lt_one k₁ k₂ l₁ p₂, norm_cC_inv_mul]
      have := b₂ (1 - u₁) u₂ r₁ up₁' c2 up₂
      rw [im₁'] at this
      exact fin 2 _ A₂ B₂ _ (by norm_num) (by norm_num) (norm_nonneg _) hA₂ wA₂ wB₂ S0 this
  ·
    have l₂ : u₂.re < 1 := by linarith
    have r₂ : 1 / 2 ≤ (1 - u₂).re := by rw [Complex.sub_re, Complex.one_re]; linarith
    have p₂' : 0 < (1 - u₂).re := by linarith
    rw [h.EC_of_re_lt_one k₁ k₂ u₁ l₂, norm_cC_inv_mul]
    rcases le_or_gt (1 / 2) u₁.re with c1 | c1
    · have p₁ : 0 < u₁.re := by linarith
      rw [E₁C_of_re_pos _ _ _ p₁]
      have := b₃ u₁ (1 - u₂) c1 up₁ r₂ up₂'
      rw [im₂'] at this
      exact fin 2 _ A₃ B₃ _ (by norm_num) (by norm_num) (norm_nonneg _) hA₃ wA₃ wB₃ S0 this
    · have l₁ : u₁.re < 1 := by linarith
      have r₁ : 1 / 2 ≤ (1 - u₁).re := by rw [Complex.sub_re, Complex.one_re]; linarith
      rw [h.F₂C.E₁C_of_re_lt_one k₁ k₂ l₁ p₂', norm_cC_inv_mul, show ∀ X : ℝ, 2 * (2 * X) = 4 * X from
        fun X => by ring]
      have := b₄ (1 - u₁) (1 - u₂) r₁ up₁' r₂ up₂'
      rw [im₁', im₂'] at this
      exact fin 4 _ A₄ B₄ _ (by norm_num) le_rfl (norm_nonneg _) hA₄ wA₄ wB₄ S0 this

end W3C

end TateComplex

end

end

section

noncomputable section

open Complex MeasureTheory Set LanglandsTunnell.TateLocal LanglandsTunnell.ArchPlace

namespace TateComplex

namespace W3C

private theorem kerC_unit_mul {u : ℂ} (hu : ‖u‖ = 1) (k : ℤ) (w y : ℂ) : kerC k w (u * y) = u ^ k * kerC k w y := by
  unfold kerC
  rw [norm_mul, hu, one_mul, mul_div_assoc, mul_zpow]
  ring

private theorem ne_zero_of_norm_eq_one {u : ℂ} (hu : ‖u‖ = 1) : u ≠ 0 := fun h0 => by
  rw [h0, norm_zero] at hu
  exact zero_ne_one hu

private theorem tateZetaC_comp_unit_mul {u : ℂ} (hu : ‖u‖ = 1) (f : ℂ → ℂ) (k : ℤ) (w : ℂ) :
    tateZetaC (fun z => f (u * z)) k w = (u ^ k)⁻¹ * tateZetaC f k w := by
  have hu0 := ne_zero_of_norm_eq_one hu
  have hu' : ‖u⁻¹‖ = 1 := by rw [norm_inv, hu, inv_one]
  rw [tateZetaC_eq_integral_ker, tateZetaC_eq_integral_ker]
  have e : (fun z : ℂ => f (u * z) * kerC k w z) = fun z => (fun y : ℂ => f y * kerC k w (u⁻¹ * y)) (u * z) := by
    funext z
    simp only
    rw [← mul_assoc, inv_mul_cancel₀ hu0, one_mul]
  rw [e, integral_comp_mul_left_C (fun y : ℂ => f y * kerC k w (u⁻¹ * y)) u, hu, one_pow, inv_one, one_smul,
    ← integral_const_mul]
  congr 1
  funext y
  rw [kerC_unit_mul hu' k w y, inv_zpow]
  ring

private theorem ClsC.ZC_rot {Ψ : ℂ → ℂ → ℂ} (h : ClsC Ψ) {u : ℂ} (hu : ‖u‖ = 1) (k₁ k₂ : ℤ) {w₁ w₂ : ℂ}
    (h₁ : 0 < w₁.re) (h₂ : 0 < w₂.re) :
    ZC (fun z t => Ψ (u * z) t) k₁ k₂ w₁ w₂ = (u ^ k₁)⁻¹ * ZC Ψ k₁ k₂ w₁ w₂ := by
  rw [(h.rot hu).ZC_eq_iterated k₁ k₂ h₁ h₂, h.ZC_eq_iterated k₁ k₂ h₁ h₂, ← integral_const_mul]
  congr 1
  funext t
  rw [tateZetaC_comp_unit_mul hu (fun z => Ψ z t) k₁ w₁]
  ring

private theorem ClsC.EC_rot {Ψ : ℂ → ℂ → ℂ} (h : ClsC Ψ) {u : ℂ} (hu : ‖u‖ = 1) (k₁ k₂ : ℤ) (w₁ w₂ : ℂ) :
    EC (fun z t => Ψ (u * z) t) k₁ k₂ w₁ w₂ = (u ^ k₁)⁻¹ * EC Ψ k₁ k₂ w₁ w₂ := by
  refine ext_EC (f := fun w₁ w₂ => EC (fun z t => Ψ (u * z) t) k₁ k₂ w₁ w₂)
    (g := fun w₁ w₂ => (u ^ k₁)⁻¹ * EC Ψ k₁ k₂ w₁ w₂)
    (fun w₂ => (h.rot hu).differentiable_EC_fst k₁ k₂ w₂) (fun w₂ => (h.differentiable_EC_fst k₁ k₂ w₂).const_mul _)
    (fun w₁ => (h.rot hu).differentiable_EC_snd k₁ k₂ w₁) (fun w₁ => (h.differentiable_EC_snd k₁ k₂ w₁).const_mul _)
    ?_ w₁ w₂
  intro v₁ v₂ h₁ h₂
  try simp only
  rw [EC_of_re_pos _ _ _ _ h₂, E₁C_of_re_pos _ _ _ h₁, EC_of_re_pos _ _ _ _ h₂, E₁C_of_re_pos _ _ _ h₁]
  unfold EchartC
  rw [h.ZC_rot hu k₁ k₂ h₁ h₂]
  ring

private theorem ClsC.EC_eq_zero_of_rot {Ψ : ℂ → ℂ → ℂ} (h : ClsC Ψ) {m : ℤ}
    (hrot : ∀ u : ℂ, ‖u‖ = 1 → (fun z t => Ψ (u * z) t) = fun z t => u ^ m * Ψ z t) {k₁ : ℤ}
    (hk : m + k₁ ≠ 0) (k₂ : ℤ) (w₁ w₂ : ℂ) : EC Ψ k₁ k₂ w₁ w₂ = 0 := by
  have hnR : ((m + k₁ : ℤ) : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hk
  set u : ℂ := cexp (((Real.pi / ((m + k₁ : ℤ) : ℝ) : ℝ) : ℂ) * I) with hu_def
  have hu : ‖u‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hu0 := ne_zero_of_norm_eq_one hu
  have hk0 : u ^ k₁ ≠ 0 := zpow_ne_zero _ hu0
  have eR : ((m + k₁ : ℤ) : ℝ) * (Real.pi / ((m + k₁ : ℤ) : ℝ)) = Real.pi := by field_simp
  have e : ((m + k₁ : ℤ) : ℂ) * ((((Real.pi / ((m + k₁ : ℤ) : ℝ) : ℝ)) : ℂ) * I) = Real.pi * I := by
    rw [← Complex.ofReal_intCast, ← mul_assoc, ← Complex.ofReal_mul, eR]
  have hun : u ^ (m + k₁) = -1 := by
    rw [hu_def, ← Complex.exp_int_mul, e]
    exact Complex.exp_pi_mul_I
  have e2 : u ^ m * u ^ k₁ = -1 := by rw [← zpow_add₀ hu0, hun]
  have h1 : (u ^ k₁)⁻¹ * EC Ψ k₁ k₂ w₁ w₂ = u ^ m * EC Ψ k₁ k₂ w₁ w₂ := by
    rw [← h.EC_rot hu k₁ k₂ w₁ w₂, ← h.EC_smul (u ^ m) k₁ k₂ w₁ w₂, hrot u hu]
  have h0 : u ^ k₁ * (u ^ k₁)⁻¹ = 1 := mul_inv_cancel₀ hk0
  linear_combination (u ^ k₁ / 2) * h1 + (-(EC Ψ k₁ k₂ w₁ w₂) / 2) * h0 + (EC Ψ k₁ k₂ w₁ w₂ / 2) * e2

private theorem complexTestFun_unit_mul {u : ℂ} (hu : ‖u‖ = 1) (k : ℤ) (z : ℂ) :
    complexTestFun k (u * z) = u ^ (-k) * complexTestFun k z := by
  have hu0 := ne_zero_of_norm_eq_one hu
  have hcu : starRingEnd ℂ u = u⁻¹ := by
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hu]
    simp
  have hpow : u⁻¹ ^ k.toNat * u ^ (-k).toNat = u ^ (-k) := by
    rw [← zpow_natCast, ← zpow_natCast, inv_zpow', ← zpow_add₀ hu0]
    congr 1
    omega
  unfold complexTestFun
  simp only [map_mul, hcu, norm_mul, hu, one_mul, mul_pow]
  rw [← hpow]
  ring

private theorem gexpC_conj₂ (α₁ α₂ : ℝ) (γr γi b₁ b₁' b₂ b₂' z t : ℂ) :
    gexpC α₁ α₂ γr γi b₁ b₁' b₂ b₂' (starRingEnd ℂ z) (starRingEnd ℂ t)
      = gexpC α₁ α₂ (starRingEnd ℂ γr) (starRingEnd ℂ γi) b₁' b₁ b₂' b₂ z t := by
  simp only [gexpC, Complex.norm_conj, Complex.conj_conj]
  ring

private theorem AdmC.conj₂ {α₁ α₂ : ℝ} {γr γi : ℂ} (h : AdmC α₁ α₂ γr γi) :
    AdmC α₁ α₂ (starRingEnd ℂ γr) (starRingEnd ℂ γi) :=
  ⟨h.h₁, h.h₂, by rw [← map_mul, h.hγ, map_zero], by rw [Complex.norm_conj]; exact h.hpd⟩

private theorem ClsC.conj₂ {Ψ : ℂ → ℂ → ℂ} (h : ClsC Ψ) : ClsC (fun z t => Ψ (starRingEnd ℂ z) (starRingEnd ℂ t)) := by
  induction h with
  | @gen α₁ α₂ γr γi b₁ b₁' b₂ b₂' hadm =>
    refine (ClsC.gen b₁' b₁ b₂' b₂ hadm.conj₂).congr ?_
    funext z t
    simp only [genC]
    rw [gexpC_conj₂]
  | smul c _ ih => exact ih.smul c
  | add _ _ ih₁ ih₂ => exact ih₁.add ih₂
  | mulZ _ ih => exact ih.mulZbar
  | mulZbar _ ih => exact ih.mulZ.congr (by funext z t; simp only [Complex.conj_conj])
  | mulT _ ih => exact ih.mulTbar
  | mulTbar _ ih => exact ih.mulT.congr (by funext z t; simp only [Complex.conj_conj])

private theorem ZC_conj₂ (Ψ : ℂ → ℂ → ℂ) (k₁ k₂ : ℤ) (w₁ w₂ : ℂ) :
    ZC (fun z t => Ψ (starRingEnd ℂ z) (starRingEnd ℂ t)) k₁ k₂ w₁ w₂ = ZC Ψ (-k₁) (-k₂) w₁ w₂ := by
  unfold ZC
  have hmp : MeasurePreserving (Prod.map Complex.conjLIE Complex.conjLIE : ℂ × ℂ → ℂ × ℂ)
      ((volume : Measure ℂ).prod volume) ((volume : Measure ℂ).prod volume) :=
    Complex.conjLIE.measurePreserving.prod Complex.conjLIE.measurePreserving
  have hme : MeasurableEmbedding (Prod.map Complex.conjLIE Complex.conjLIE : ℂ × ℂ → ℂ × ℂ) :=
    (Complex.conjLIE.toHomeomorph.prodCongr Complex.conjLIE.toHomeomorph).measurableEmbedding
  have e : zintC (fun z t => Ψ (starRingEnd ℂ z) (starRingEnd ℂ t)) k₁ k₂ w₁ w₂
      = fun p => (fun q : ℂ × ℂ => Ψ q.1 q.2 * kerC k₁ w₁ (starRingEnd ℂ q.1) * kerC k₂ w₂ (starRingEnd ℂ q.2))
          (Prod.map Complex.conjLIE Complex.conjLIE p) := by
    funext p
    simp only [zintC, Prod.map_fst, Prod.map_snd, Complex.conjLIE_apply, Complex.conj_conj]
  rw [Measure.volume_eq_prod, e, hmp.integral_comp hme]
  refine integral_congr_ae (ae_off_axes_C.mono fun q hq => ?_)
  simp only [zintC, kerC_conj hq.1, kerC_conj hq.2]

private theorem ClsC.EC_conj₂ {Ψ : ℂ → ℂ → ℂ} (h : ClsC Ψ) (k₁ k₂ : ℤ) (w₁ w₂ : ℂ) :
    EC (fun z t => Ψ (starRingEnd ℂ z) (starRingEnd ℂ t)) k₁ k₂ w₁ w₂ = EC Ψ (-k₁) (-k₂) w₁ w₂ := by
  refine ext_EC (f := fun w₁ w₂ => EC (fun z t => Ψ (starRingEnd ℂ z) (starRingEnd ℂ t)) k₁ k₂ w₁ w₂)
    (g := fun w₁ w₂ => EC Ψ (-k₁) (-k₂) w₁ w₂)
    (fun w₂ => h.conj₂.differentiable_EC_fst k₁ k₂ w₂) (fun w₂ => h.differentiable_EC_fst (-k₁) (-k₂) w₂)
    (fun w₁ => h.conj₂.differentiable_EC_snd k₁ k₂ w₁) (fun w₁ => h.differentiable_EC_snd (-k₁) (-k₂) w₁)
    ?_ w₁ w₂
  intro v₁ v₂ h₁ h₂
  try simp only
  rw [EC_of_re_pos _ _ _ _ h₂, E₁C_of_re_pos _ _ _ h₁, EC_of_re_pos _ _ _ _ h₂, E₁C_of_re_pos _ _ _ h₁]
  unfold EchartC
  rw [ZC_conj₂, Int.natAbs_neg, Int.natAbs_neg]

end W3C

end TateComplex

end

end

section

open Complex LanglandsTunnell

namespace TateComplex
namespace Datum

private theorem twist_eq (P : ComplexArchParam) (u : ℂ) (k : ℤ) :
    P.twist u k = ⟨P.u₁ + u, P.k₁ + k, P.u₂ + u, P.k₂ + k⟩ := rfl

private theorem archFactor_twist (P : ComplexArchParam) (u : ℂ) (k : ℤ) (s : ℂ) :
    (P.twist u k).archFactor s
      = Gammaℂ (s + (P.u₁ + u + ((P.k₁ + k).natAbs : ℂ) / 2))
          * Gammaℂ (s + (P.u₂ + u + ((P.k₂ + k).natAbs : ℂ) / 2)) := by
  simp [ComplexArchParam.twist, ComplexArchParam.archFactor, ComplexArchParam.gammaC]

private theorem archFactor_twist' (P : ComplexArchParam) (u : ℂ) (k : ℤ) (s : ℂ) :
    (P.twist u k).archFactor s
      = Gammaℂ (s + u + P.u₁ + ((k + P.k₁).natAbs : ℂ) / 2) * Gammaℂ (s + u + P.u₂ + ((k + P.k₂).natAbs : ℂ) / 2) := by
  rw [archFactor_twist, add_comm P.k₁ k, add_comm P.k₂ k]
  congr 1 <;> congr 1 <;> ring

private theorem epsilonFactor_twist (P : ComplexArchParam) (u : ℂ) (k : ℤ) :
    (P.twist u k).epsilonFactor = I ^ (k + P.k₁).natAbs * I ^ (k + P.k₂).natAbs := by
  simp only [ComplexArchParam.epsilonFactor, ComplexArchParam.twist, add_comm k]

private theorem centralExponent_eq (P : ComplexArchParam) : P.centralExponent = P.u₁ + P.u₂ := rfl

private theorem centralTwist_eq (P : ComplexArchParam) : P.centralTwist = P.k₁ + P.k₂ := rfl

private theorem neg_add_centralTwist_add_left (P : ComplexArchParam) (k : ℤ) :
    -(k + P.centralTwist) + P.k₁ = -(k + P.k₂) := by
  rw [centralTwist_eq]; ring

private theorem neg_add_centralTwist_add_right (P : ComplexArchParam) (k : ℤ) :
    -(k + P.centralTwist) + P.k₂ = -(k + P.k₁) := by
  rw [centralTwist_eq]; ring

private theorem neg_add_centralExponent_add_left (P : ComplexArchParam) (u : ℂ) :
    -(u + P.centralExponent) + P.u₁ = -(u + P.u₂) := by
  rw [centralExponent_eq]; ring

private theorem neg_add_centralExponent_add_right (P : ComplexArchParam) (u : ℂ) :
    -(u + P.centralExponent) + P.u₂ = -(u + P.u₁) := by
  rw [centralExponent_eq]; ring

private theorem centralChar_eq (P : ComplexArchParam) (z : ℂ) :
    Converse.ArchC.centralChar P z
      = ((‖z‖ : ℝ) : ℂ) ^ (2 * (P.u₁ + P.u₂)) * (z / ((‖z‖ : ℝ) : ℂ)) ^ (P.k₁ + P.k₂) := rfl

private theorem cC_eq (b : ℤ) : cC b = (-I) ^ b.natAbs / 2 := rfl

private theorem cC_ne_zero (b : ℤ) : cC b ≠ 0 := by
  rw [cC_eq]
  exact div_ne_zero (pow_ne_zero _ (neg_ne_zero.2 I_ne_zero)) two_ne_zero

private theorem neg_one_pow_mul_neg_I_pow (n : ℕ) : (-1 : ℂ) ^ n * (-I) ^ n = I ^ n := by
  rw [← mul_pow, neg_one_mul, neg_neg]

private theorem neg_I_pow_inv (n : ℕ) : ((-I) ^ n)⁻¹ = I ^ n := by
  rw [← inv_pow, inv_neg, Complex.inv_I, neg_neg]

private theorem neg_one_pow_mul_cC_div_cC (b₁ b₂ : ℤ) :
    (-1 : ℂ) ^ b₁.natAbs * cC b₁ / cC b₂ = I ^ b₁.natAbs * I ^ b₂.natAbs := by
  have h₁ : (-I) ^ b₁.natAbs ≠ 0 := pow_ne_zero _ (neg_ne_zero.2 I_ne_zero)
  have h₂ : (-I) ^ b₂.natAbs ≠ 0 := pow_ne_zero _ (neg_ne_zero.2 I_ne_zero)
  rw [cC_eq, cC_eq, ← neg_one_pow_mul_neg_I_pow, ← neg_I_pow_inv]
  field_simp

private theorem neg_one_pow_mul_cC_div_cC_eq_epsilonFactor_twist (P : ComplexArchParam) (u : ℂ) (k : ℤ) :
    (-1 : ℂ) ^ (k + P.k₁).natAbs * cC (k + P.k₁) / cC (k + P.k₂) = (P.twist u k).epsilonFactor := by
  rw [neg_one_pow_mul_cC_div_cC, epsilonFactor_twist]

private theorem epsilonFactor_twist_neg_indices (P : ComplexArchParam) (u : ℂ) (k : ℤ) :
    I ^ (-(k + P.k₂)).natAbs * I ^ (-(k + P.k₁)).natAbs = (P.twist u k).epsilonFactor := by
  rw [epsilonFactor_twist, Int.natAbs_neg, Int.natAbs_neg, mul_comm]

end TateComplex.Datum

end

section

open Complex LanglandsTunnell LanglandsTunnell.Converse.ArchC

noncomputable section

namespace TateComplex
namespace Datum

private theorem psi_add (x y : ℂ) : psi (x + y) = psi x * psi y := by
  unfold psi; rw [← Complex.exp_add]; congr 1; push_cast; simp only [Complex.add_re]; push_cast; ring

private theorem psi_zero : psi 0 = 1 := by
  simp [psi]

private theorem norm_psi (x : ℂ) : ‖psi x‖ = 1 := by
  unfold psi
  rw [Complex.norm_exp]
  have : (2 * (Real.pi : ℂ) * I * ((2 * x.re : ℝ) : ℂ)).re = 0 := by simp
  rw [this, Real.exp_zero]

private theorem ofReal_norm_ne_zero {z : ℂ} (hz : z ≠ 0) : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by
  exact_mod_cast (norm_pos_iff.2 hz).ne'

private theorem quasiChar_ne_zero (u : ℂ) (k : ℤ) {z : ℂ} (hz : z ≠ 0) : quasiChar u k z ≠ 0 := by
  unfold quasiChar
  have h := ofReal_norm_ne_zero hz
  refine mul_ne_zero ?_ (zpow_ne_zero _ (div_ne_zero hz h))
  rw [Complex.cpow_def_of_ne_zero h]
  exact Complex.exp_ne_zero _

private theorem quasiChar_mul (u u' : ℂ) (k k' : ℤ) {z : ℂ} (hz : z ≠ 0) :
    quasiChar u k z * quasiChar u' k' z = quasiChar (u + u') (k + k') z := by
  unfold quasiChar
  have h := ofReal_norm_ne_zero hz
  rw [mul_add, Complex.cpow_add _ _ h, zpow_add₀ (div_ne_zero hz h)]
  ring

private theorem quasiChar_zero_zero (z : ℂ) : quasiChar 0 0 z = 1 := by
  unfold quasiChar
  simp

private theorem centralChar_eq_mul (P : ComplexArchParam) {z : ℂ} (hz : z ≠ 0) :
    centralChar P z = quasiChar P.u₁ P.k₁ z * quasiChar P.u₂ P.k₂ z := by
  rw [quasiChar_mul _ _ _ _ hz]; rfl

private theorem quasiChar_eq_sq_cpow (u : ℂ) (k : ℤ) {z : ℂ} (hz : z ≠ 0) :
    quasiChar u k z = (z / ((‖z‖ : ℝ) : ℂ)) ^ k * ((‖z‖ ^ 2 : ℝ) : ℂ) ^ u := by
  unfold quasiChar
  rw [ofReal_sq_cpow (norm_pos_iff.2 hz) u, mul_comm]

private theorem zetaIntegrand_eq_kerC (W : Matrix (Fin 2) (Fin 2) ℂ → ℂ) (g : Matrix (Fin 2) (Fin 2) ℂ) (u : ℂ) (k : ℤ)
    (s : ℂ) {z : ℂ} (hz : z ≠ 0) :
    zetaIntegrand W g u k s z = W (diagOne z * g) * kerC k (s + u - 1) z := by
  have hm : ((‖z‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (pow_pos (norm_pos_iff.2 hz) 2).ne'
  unfold zetaIntegrand kerC
  rw [quasiChar_eq_sq_cpow u k hz, ← Complex.cpow_neg_one, show s + u - 1 - 1 = u + (s - 1) + (-1 : ℂ) by ring,
    Complex.cpow_add _ _ hm, Complex.cpow_add _ _ hm]
  ring

private theorem det_weyl : weyl.det = 1 := by
  norm_num [weyl, Matrix.det_fin_two_of]

private theorem det_weyl_mul (g : Matrix (Fin 2) (Fin 2) ℂ) : (weyl * g).det = g.det := by
  rw [Matrix.det_mul, det_weyl, one_mul]

private theorem det_unip (x : ℂ) : (unip x).det = 1 := by
  simp [unip, Matrix.det_fin_two_of]

private theorem det_unip_mul (x : ℂ) (g : Matrix (Fin 2) (Fin 2) ℂ) : (unip x * g).det = g.det := by
  rw [Matrix.det_mul, det_unip, one_mul]

private theorem det_diagOne (z : ℂ) : (diagOne z).det = z := by
  simp [diagOne, Matrix.det_fin_two_of]

private theorem det_diagOne_mul (z : ℂ) (g : Matrix (Fin 2) (Fin 2) ℂ) : (diagOne z * g).det = z * g.det := by
  rw [Matrix.det_mul, det_diagOne]

private theorem det_smul_two (z : ℂ) (g : Matrix (Fin 2) (Fin 2) ℂ) : (z • g).det = z ^ 2 * g.det := by
  rw [Matrix.det_smul]; simp

private theorem weyl_mul_entries (g : Matrix (Fin 2) (Fin 2) ℂ) :
    (weyl * g) 0 0 = g 1 0 ∧ (weyl * g) 0 1 = g 1 1 ∧ (weyl * g) 1 0 = -g 0 0 ∧ (weyl * g) 1 1 = -g 0 1 := by
  simp [weyl, Matrix.mul_apply, Fin.sum_univ_two]

private theorem unip_mul_entries (x : ℂ) (g : Matrix (Fin 2) (Fin 2) ℂ) :
    (unip x * g) 0 0 = g 0 0 + x * g 1 0 ∧ (unip x * g) 0 1 = g 0 1 + x * g 1 1
      ∧ (unip x * g) 1 0 = g 1 0 ∧ (unip x * g) 1 1 = g 1 1 := by
  simp [unip, Matrix.mul_apply, Fin.sum_univ_two]

private theorem re_pos_of_abscissa_lt (P : ComplexArchParam) {u s : ℂ} (hs : max (-P.u₁.re) (-P.u₂.re) < s.re + u.re) :
    0 < (s + u + P.u₁).re ∧ 0 < (s + u + P.u₂).re := by
  have m₁ := le_max_left (-P.u₁.re) (-P.u₂.re)
  have m₂ := le_max_right (-P.u₁.re) (-P.u₂.re)
  simp only [Complex.add_re]
  constructor <;> linarith

end TateComplex.Datum

end

end

section

open Complex LanglandsTunnell LanglandsTunnell.ArchPlace

noncomputable section

namespace TateComplex
namespace Datum

open W3C

private def PsiC (P : ComplexArchParam) (g : Matrix (Fin 2) (Fin 2) ℂ) (z t : ℂ) : ℂ :=
  complexTestFun P.k₁ (-(t * g 0 0 + z * g 1 0)) * complexTestFun (-P.k₂) (-(t * g 0 1 + z * g 1 1))

private theorem ofReal_norm_sq_eq_mul_conj (x : ℂ) : ((‖x‖ ^ 2 : ℝ) : ℂ) = x * starRingEnd ℂ x := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

private theorem _root_.P2MW.S_LanglandsTunnell_Converse_exists_archDatumC_W_ne_zero.TateComplex.W3C.ClsC.linear_mul {Ψ : ℂ → ℂ → ℂ} (h : ClsC Ψ) (a b : ℂ) :
    ClsC (fun z t => (a * z + b * t) * Ψ z t) :=
  (ClsC.add (ClsC.smul a h.mulZ) (ClsC.smul b h.mulT)).congr (by funext z t; ring)

private theorem _root_.P2MW.S_LanglandsTunnell_Converse_exists_archDatumC_W_ne_zero.TateComplex.W3C.ClsC.conj_linear_mul {Ψ : ℂ → ℂ → ℂ} (h : ClsC Ψ) (a b : ℂ) :
    ClsC (fun z t => (a * starRingEnd ℂ z + b * starRingEnd ℂ t) * Ψ z t) :=
  (ClsC.add (ClsC.smul a h.mulZbar) (ClsC.smul b h.mulTbar)).congr (by funext z t; ring)

private theorem _root_.P2MW.S_LanglandsTunnell_Converse_exists_archDatumC_W_ne_zero.TateComplex.W3C.ClsC.linear_pow_mul {Ψ : ℂ → ℂ → ℂ} (h : ClsC Ψ) (a b : ℂ) (n : ℕ) :
    ClsC (fun z t => (a * z + b * t) ^ n * Ψ z t) := by
  induction n with
  | zero => exact h.congr (by funext z t; simp)
  | succ n ih => exact (ih.linear_mul a b).congr (by funext z t; ring)

private theorem _root_.P2MW.S_LanglandsTunnell_Converse_exists_archDatumC_W_ne_zero.TateComplex.W3C.ClsC.conj_linear_pow_mul {Ψ : ℂ → ℂ → ℂ} (h : ClsC Ψ) (a b : ℂ) (n : ℕ) :
    ClsC (fun z t => (a * starRingEnd ℂ z + b * starRingEnd ℂ t) ^ n * Ψ z t) := by
  induction n with
  | zero => exact h.congr (by funext z t; simp)
  | succ n ih => exact (ih.conj_linear_mul a b).congr (by funext z t; ring)

private theorem complexTestFun_linear (k : ℤ) (a b z t : ℂ) :
    complexTestFun k (a * z + b * t)
      = (starRingEnd ℂ a * starRingEnd ℂ z + starRingEnd ℂ b * starRingEnd ℂ t) ^ k.toNat
          * ((a * z + b * t) ^ (-k).toNat * cexp (-(2 * Real.pi * ‖a * z + b * t‖ ^ 2))) := by
  simp only [complexTestFun, map_add, map_mul]
  ring

private def alphaOne (g : Matrix (Fin 2) (Fin 2) ℂ) : ℝ := ‖g 1 0‖ ^ 2 + ‖g 1 1‖ ^ 2

private def alphaTwo (g : Matrix (Fin 2) (Fin 2) ℂ) : ℝ := ‖g 0 0‖ ^ 2 + ‖g 0 1‖ ^ 2

private def
    gammaR (g : Matrix (Fin 2) (Fin 2) ℂ) : ℂ := -(g 1 0 * starRingEnd ℂ (g 0 0) + g 1 1 * starRingEnd ℂ (g 0 1))

private theorem alphaOne_mul_alphaTwo_sub (g : Matrix (Fin 2) (Fin 2) ℂ) :
    alphaOne g * alphaTwo g - ‖gammaR g‖ ^ 2 = ‖g.det‖ ^ 2 := by
  simp only [alphaOne, alphaTwo, gammaR, Matrix.det_fin_two, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
    Complex.neg_re, Complex.neg_im, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re,
    Complex.sub_im, Complex.conj_re, Complex.conj_im]
  ring

private theorem admC_of_det_ne_zero {g : Matrix (Fin 2) (Fin 2) ℂ} (hg : g.det ≠ 0) :
    AdmC (alphaOne g) (alphaTwo g) (gammaR g) 0 := by
  have hdet : 0 < ‖g.det‖ ^ 2 := by positivity
  have hL := alphaOne_mul_alphaTwo_sub g
  have h10 : g 1 0 ≠ 0 ∨ g 1 1 ≠ 0 := by
    by_contra h
    push Not at h
    exact hg (by rw [Matrix.det_fin_two, h.1, h.2]; ring)
  have h00 : g 0 0 ≠ 0 ∨ g 0 1 ≠ 0 := by
    by_contra h
    push Not at h
    exact hg (by rw [Matrix.det_fin_two, h.1, h.2]; ring)
  refine ⟨?_, ?_, mul_zero _, by linarith⟩
  · unfold alphaOne
    rcases h10 with h | h
    · have := norm_pos_iff.2 h; positivity
    · have := norm_pos_iff.2 h; positivity
  · unfold alphaTwo
    rcases h00 with h | h
    · have := norm_pos_iff.2 h; positivity
    · have := norm_pos_iff.2 h; positivity

private theorem gaussian_exponent_eq (g : Matrix (Fin 2) (Fin 2) ℂ) (z t : ℂ) :
    -(2 * (Real.pi : ℂ) * ‖g 1 0 * z + g 0 0 * t‖ ^ 2) + -(2 * (Real.pi : ℂ) * ‖g 1 1 * z + g 0 1 * t‖ ^ 2)
      = gexpC (alphaOne g) (alphaTwo g) (gammaR g) 0 0 0 0 0 z t := by
  have e1 : ((‖g 1 0 * z + g 0 0 * t‖ ^ 2 : ℝ) : ℂ)
      = (g 1 0 * z + g 0 0 * t) * starRingEnd ℂ (g 1 0 * z + g 0 0 * t) := ofReal_norm_sq_eq_mul_conj _
  have e2 : ((‖g 1 1 * z + g 0 1 * t‖ ^ 2 : ℝ) : ℂ)
      = (g 1 1 * z + g 0 1 * t) * starRingEnd ℂ (g 1 1 * z + g 0 1 * t) := ofReal_norm_sq_eq_mul_conj _
  have ez : ((‖z‖ ^ 2 : ℝ) : ℂ) = z * starRingEnd ℂ z := ofReal_norm_sq_eq_mul_conj z
  have et : ((‖t‖ ^ 2 : ℝ) : ℂ) = t * starRingEnd ℂ t := ofReal_norm_sq_eq_mul_conj t
  have ea : ∀ x : ℂ, ((‖x‖ ^ 2 : ℝ) : ℂ) = x * starRingEnd ℂ x := ofReal_norm_sq_eq_mul_conj
  simp only [gexpC, alphaOne, alphaTwo, gammaR]
  push_cast
  rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, e1, e2]
  simp only [← Complex.ofReal_pow, ez, et, ea, map_add, map_mul, map_neg, Complex.conj_conj]
  simp only [map_zero, mul_zero, zero_mul, add_zero, zero_add]
  ring

private theorem clsC_gaussian {g : Matrix (Fin 2) (Fin 2) ℂ} (hg : g.det ≠ 0) :
    ClsC (fun z t => cexp (-(2 * Real.pi * ‖-(t * g 0 0 + z * g 1 0)‖ ^ 2))
      * cexp (-(2 * Real.pi * ‖-(t * g 0 1 + z * g 1 1)‖ ^ 2))) := by
  refine (ClsC.gen 0 0 0 0 (admC_of_det_ne_zero hg)).congr ?_
  funext z t
  simp only [genC]
  rw [← gaussian_exponent_eq, Complex.exp_add, norm_neg, norm_neg]
  congr 2 <;> congr 3 <;> ring

private theorem
    clsC_PsiC (P : ComplexArchParam) {g : Matrix (Fin 2) (Fin 2) ℂ} (hg : g.det ≠ 0) : ClsC (PsiC P g) := by
  have h0 := clsC_gaussian hg
  have h1 := h0.conj_linear_pow_mul (starRingEnd ℂ (-g 1 0)) (starRingEnd ℂ (-g 0 0)) P.k₁.toNat
  have h2 := h1.linear_pow_mul (-g 1 0) (-g 0 0) (-P.k₁).toNat
  have h3 := h2.conj_linear_pow_mul (starRingEnd ℂ (-g 1 1)) (starRingEnd ℂ (-g 0 1)) (-P.k₂).toNat
  have h4 := h3.linear_pow_mul (-g 1 1) (-g 0 1) (-(-P.k₂)).toNat
  refine h4.congr ?_
  funext z t
  simp only [PsiC]
  rw [show -(t * g 0 0 + z * g 1 0) = -g 1 0 * z + -g 0 0 * t by ring,
    show -(t * g 0 1 + z * g 1 1) = -g 1 1 * z + -g 0 1 * t by ring, complexTestFun_linear, complexTestFun_linear]
  rw [show ‖-g 1 0 * z + -g 0 0 * t‖ = ‖-(t * g 0 0 + z * g 1 0)‖ by congr 1; ring,
    show ‖-g 1 1 * z + -g 0 1 * t‖ = ‖-(t * g 0 1 + z * g 1 1)‖ by congr 1; ring]
  ring

end TateComplex.Datum

end

end

section

open Complex MeasureTheory LanglandsTunnell LanglandsTunnell.ArchPlace LanglandsTunnell.Converse.ArchC

noncomputable section

namespace TateComplex
namespace Datum

variable (P : ComplexArchParam)

private def innerWC (h : Matrix (Fin 2) (Fin 2) ℂ) (t : ℂ) : ℂ :=
  ∫ z : ℂ, complexTestFun P.k₁ (-(t * (h 0 0 + z * h 1 0))) * complexTestFun (-P.k₂) (-(t * (h 0 1 + z * h 1 1)))
    * psi (-z)

private def WmemC (g : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  ((‖g.det‖ ^ 2 : ℝ) : ℂ) * quasiChar P.u₁ P.k₁ g.det
    * ∫ t : ℂ, innerWC P g t * quasiChar (P.u₁ - P.u₂) (P.k₁ - P.k₂) t

private theorem
    quasiChar_mul_arg (u : ℂ) (k : ℤ) (a b : ℂ) : quasiChar u k (a * b) = quasiChar u k a * quasiChar u k b := by
  unfold quasiChar
  rw [norm_mul, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (norm_nonneg a) (norm_nonneg b),
    mul_div_mul_comm, mul_zpow]
  ring

private theorem quasiChar_sq_eq {c : ℂ} (hc : c ≠ 0) :
    quasiChar P.u₁ P.k₁ c * quasiChar P.u₁ P.k₁ c
      = quasiChar (P.u₁ - P.u₂) (P.k₁ - P.k₂) c * quasiChar (P.u₁ + P.u₂) (P.k₁ + P.k₂) c := by
  rw [quasiChar_mul _ _ _ _ hc, quasiChar_mul _ _ _ _ hc]
  rw [show P.u₁ - P.u₂ + (P.u₁ + P.u₂) = P.u₁ + P.u₁ by ring, show P.k₁ - P.k₂ + (P.k₁ + P.k₂) = P.k₁ + P.k₁ by ring]

private theorem innerWC_unip (x₀ : ℂ) (m : Matrix (Fin 2) (Fin 2) ℂ) (t : ℂ) :
    innerWC P (unip x₀ * m) t = psi x₀ * innerWC P m t := by
  unfold innerWC
  obtain ⟨h00, h01, h10, h11⟩ := unip_mul_entries x₀ m
  simp only [h00, h01, h10, h11]
  set f : ℂ → ℂ := fun z =>
    complexTestFun P.k₁ (-(t * (m 0 0 + z * m 1 0))) * complexTestFun (-P.k₂) (-(t * (m 0 1 + z * m 1 1))) * psi (-z)
    with hf
  have hshift : (fun z : ℂ =>
      complexTestFun P.k₁ (-(t * (m 0 0 + x₀ * m 1 0 + z * m 1 0)))
        * complexTestFun (-P.k₂) (-(t * (m 0 1 + x₀ * m 1 1 + z * m 1 1))) * psi (-z))
      = fun z : ℂ => f (z + x₀) * psi x₀ := by
    funext z
    simp only [hf]
    have hpsi : psi (-z) = psi (-(z + x₀)) * psi x₀ := by
      rw [← psi_add]; congr 1; ring
    rw [hpsi, show m 0 0 + x₀ * m 1 0 + z * m 1 0 = m 0 0 + (z + x₀) * m 1 0 by ring,
      show m 0 1 + x₀ * m 1 1 + z * m 1 1 = m 0 1 + (z + x₀) * m 1 1 by ring]
    ring
  rw [hshift]
  have h1 : (∫ z : ℂ, f (z + x₀) * psi x₀) = (∫ z : ℂ, f (z + x₀)) * psi x₀ := integral_mul_const _ _
  rw [h1, integral_add_right_eq_self]
  ring

private theorem WmemC_unip (x : ℂ) (g : Matrix (Fin 2) (Fin 2) ℂ) : WmemC P (unip x * g) = psi x * WmemC P g := by
  unfold WmemC
  rw [det_unip_mul]
  simp only [innerWC_unip, mul_assoc]
  have h2 : (∫ t : ℂ, psi x * (innerWC P g t * quasiChar (P.u₁ - P.u₂) (P.k₁ - P.k₂) t))
      = psi x * ∫ t : ℂ, innerWC P g t * quasiChar (P.u₁ - P.u₂) (P.k₁ - P.k₂) t := integral_const_mul _ _
  rw [h2]
  ring

private theorem
    innerWC_smul (c : ℂ) (m : Matrix (Fin 2) (Fin 2) ℂ) (t : ℂ) : innerWC P (c • m) t = innerWC P m (c * t) := by
  unfold innerWC
  congr 1; funext z
  simp only [Matrix.smul_apply, smul_eq_mul]
  congr 3 <;> ring

private theorem WmemC_smul {c : ℂ} (hc : c ≠ 0) (g : Matrix (Fin 2) (Fin 2) ℂ) :
    WmemC P (c • g) = quasiChar (P.u₁ + P.u₂) (P.k₁ + P.k₂) c * ((‖c‖ ^ 2 : ℝ) : ℂ) * WmemC P g := by
  unfold WmemC
  rw [det_smul_two]
  have hqz : quasiChar (P.u₁ - P.u₂) (P.k₁ - P.k₂) c ≠ 0 := quasiChar_ne_zero _ _ hc
  have hc2 : ((‖c‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (pow_pos (norm_pos_iff.2 hc) 2).ne'
  have hint : (∫ t : ℂ, innerWC P (c • g) t * quasiChar (P.u₁ - P.u₂) (P.k₁ - P.k₂) t)
      = (quasiChar (P.u₁ - P.u₂) (P.k₁ - P.k₂) c)⁻¹ * (((‖c‖ ^ 2 : ℝ) : ℂ))⁻¹
          * ∫ t : ℂ, innerWC P g t * quasiChar (P.u₁ - P.u₂) (P.k₁ - P.k₂) t := by
    have h1 : (fun t : ℂ => innerWC P (c • g) t * quasiChar (P.u₁ - P.u₂) (P.k₁ - P.k₂) t)
        = fun t : ℂ => (quasiChar (P.u₁ - P.u₂) (P.k₁ - P.k₂) c)⁻¹
            * (innerWC P g (c * t) * quasiChar (P.u₁ - P.u₂) (P.k₁ - P.k₂) (c * t)) := by
      funext t
      rw [innerWC_smul, quasiChar_mul_arg]
      field_simp
    rw [h1, integral_const_mul]
    have h3 : (∫ t : ℂ, innerWC P g (c * t) * quasiChar (P.u₁ - P.u₂) (P.k₁ - P.k₂) (c * t))
        = (‖c‖ ^ 2)⁻¹ • ∫ t : ℂ, innerWC P g t * quasiChar (P.u₁ - P.u₂) (P.k₁ - P.k₂) t :=
      integral_comp_mul_left_C (fun t : ℂ => innerWC P g t * quasiChar (P.u₁ - P.u₂) (P.k₁ - P.k₂) t) c
    rw [h3, Complex.real_smul]
    push_cast
    ring
  rw [hint]
  have hdet : ((‖c ^ 2 * g.det‖ ^ 2 : ℝ) : ℂ)
      = ((‖c‖ ^ 2 : ℝ) : ℂ) * ((‖c‖ ^ 2 : ℝ) : ℂ) * ((‖g.det‖ ^ 2 : ℝ) : ℂ) := by
    rw [norm_mul, norm_pow]; push_cast; ring
  have hq1 : quasiChar P.u₁ P.k₁ (c ^ 2 * g.det)
      = quasiChar P.u₁ P.k₁ c * quasiChar P.u₁ P.k₁ c * quasiChar P.u₁ P.k₁ g.det := by
    rw [quasiChar_mul_arg, pow_two, quasiChar_mul_arg]
  rw [hdet, hq1, quasiChar_sq_eq P hc]
  field_simp

private theorem WmemC_central (c : ℂ) (g : Matrix (Fin 2) (Fin 2) ℂ) (hc : c ≠ 0) :
    WmemC P (c • g) = centralChar P c * ((‖c‖ ^ 2 : ℝ) : ℂ) * WmemC P g := by
  rw [centralChar, centralExponent_eq, centralTwist_eq]
  exact WmemC_smul P hc g

end TateComplex.Datum

end

end

section

open Complex MeasureTheory LanglandsTunnell LanglandsTunnell.ArchPlace LanglandsTunnell.Converse.ArchC

noncomputable section

namespace TateComplex
namespace Datum

private theorem quasiChar_one (u : ℂ) (k : ℤ) : quasiChar u k 1 = 1 := by
  unfold quasiChar
  simp

private theorem
    quasiChar_inv_arg (u : ℂ) (k : ℤ) {z : ℂ} (hz : z ≠ 0) : quasiChar u k z⁻¹ = quasiChar (-u) (-k) z := by
  have h1 : quasiChar u k z⁻¹ * quasiChar u k z = 1 := by
    rw [← quasiChar_mul_arg, inv_mul_cancel₀ hz, quasiChar_one]
  have h2 : quasiChar (-u) (-k) z * quasiChar u k z = 1 := by
    rw [quasiChar_mul _ _ _ _ hz, neg_add_cancel, neg_add_cancel, quasiChar_zero_zero]
  exact mul_right_cancel₀ (quasiChar_ne_zero u k hz) (h1.trans h2.symm)

private theorem kerC_eq_quasiChar (k : ℤ) (w : ℂ) {z : ℂ} (hz : z ≠ 0) : kerC k w z = quasiChar (w - 1) k z := by
  rw [quasiChar_eq_sq_cpow _ _ hz, kerC]

private theorem ofReal_norm_sq_eq_quasiChar {z : ℂ} (hz : z ≠ 0) : ((‖z‖ ^ 2 : ℝ) : ℂ) = quasiChar 1 0 z := by
  rw [quasiChar_eq_sq_cpow _ _ hz, zpow_zero, one_mul, cpow_one]

private theorem ofReal_norm_sq_cpow_eq_quasiChar (w : ℂ) {z : ℂ} (hz : z ≠ 0) :
    ((‖z‖ ^ 2 : ℝ) : ℂ) ^ w = quasiChar w 0 z := by
  rw [quasiChar_eq_sq_cpow _ _ hz, zpow_zero, one_mul]

private theorem
    ofReal_norm_sq_inv_eq_quasiChar {z : ℂ} (hz : z ≠ 0) : (((‖z‖ ^ 2 : ℝ) : ℂ))⁻¹ = quasiChar (-1) 0 z := by
  rw [← ofReal_norm_sq_cpow_eq_quasiChar _ hz, cpow_neg_one]

private theorem ofReal_inv_norm_sq_eq_quasiChar {z : ℂ} (hz : z ≠ 0) :
    (((‖z‖ ^ 2)⁻¹ : ℝ) : ℂ) = quasiChar (-1) 0 z := by
  rw [Complex.ofReal_inv, ofReal_norm_sq_inv_eq_quasiChar hz]

private theorem psi_neg_eq_psiComplex (z : ℂ) : psi (-z) = psiComplex z := by
  rw [psiComplex_apply, psi, Complex.add_conj]
  congr 1
  push_cast
  simp only [Complex.neg_re]
  push_cast
  ring

private theorem FC_eq_integral (f : ℂ → ℂ) (w : ℂ) : FC f w = ∫ x : ℂ, f x * psiComplex (x * w) := rfl

variable (P : ComplexArchParam)

private theorem collect_xi (u s : ℂ) (k : ℤ) {ξ : ℂ} (hξ : ξ ≠ 0) :
    (((‖ξ‖ ^ 2)⁻¹ : ℝ) : ℂ) * (((‖ξ‖ ^ 2 : ℝ) : ℂ) * quasiChar P.u₁ P.k₁ ξ)
        * ((((‖ξ⁻¹‖ ^ 2)⁻¹ : ℝ) : ℂ) * quasiChar (P.u₁ - P.u₂) (P.k₁ - P.k₂) ξ⁻¹)
        * (quasiChar u k ξ * ((‖ξ‖ ^ 2 : ℝ) : ℂ) ^ (s - 1) * (((‖ξ‖ ^ 2 : ℝ) : ℂ))⁻¹)
      = kerC (k + P.k₂) (s + u + P.u₂) ξ := by
  have hξi : ξ⁻¹ ≠ 0 := inv_ne_zero hξ
  rw [ofReal_norm_sq_cpow_eq_quasiChar _ hξ, ofReal_norm_sq_inv_eq_quasiChar hξ, ofReal_inv_norm_sq_eq_quasiChar hξ,
    ofReal_inv_norm_sq_eq_quasiChar hξi, ofReal_norm_sq_eq_quasiChar hξ, quasiChar_inv_arg (-1) 0 hξ, neg_neg,
    neg_zero, quasiChar_inv_arg (P.u₁ - P.u₂) (P.k₁ - P.k₂) hξ, kerC_eq_quasiChar _ _ hξ]
  simp only [quasiChar_mul _ _ _ _ hξ]
  ring_nf

private theorem collect_Y (u s : ℂ) (k : ℤ) {Y : ℂ} (hY : Y ≠ 0) :
    ((‖Y‖ ^ 2 : ℝ) : ℂ) * quasiChar P.u₁ P.k₁ Y
        * (quasiChar u k Y * ((‖Y‖ ^ 2 : ℝ) : ℂ) ^ (s - 1) * (((‖Y‖ ^ 2 : ℝ) : ℂ))⁻¹)
      = kerC (k + P.k₁) (s + u + P.u₁) Y := by
  rw [ofReal_norm_sq_cpow_eq_quasiChar _ hY, ofReal_norm_sq_inv_eq_quasiChar hY, ofReal_norm_sq_eq_quasiChar hY,
    kerC_eq_quasiChar _ _ hY]
  simp only [quasiChar_mul _ _ _ _ hY]
  ring_nf

private theorem diagOne_mul_entries (y : ℂ) (g : Matrix (Fin 2) (Fin 2) ℂ) :
    (diagOne y * g) 0 0 = y * g 0 0 ∧ (diagOne y * g) 0 1 = y * g 0 1
      ∧ (diagOne y * g) 1 0 = g 1 0 ∧ (diagOne y * g) 1 1 = g 1 1 := by
  simp [diagOne, Matrix.mul_apply, Fin.sum_univ_two]

private theorem innerWC_diagOne_mul (g : Matrix (Fin 2) (Fin 2) ℂ) (y : ℂ) {t : ℂ} (ht : t ≠ 0) :
    innerWC P (diagOne y * g) t = (((‖t‖ ^ 2)⁻¹ : ℝ) : ℂ) * FC (fun x => PsiC P g x (t * y)) t⁻¹ := by
  unfold innerWC
  obtain ⟨h00, h01, h10, h11⟩ := diagOne_mul_entries y g
  simp only [h00, h01, h10, h11]
  have e : (fun z : ℂ => complexTestFun P.k₁ (-(t * (y * g 0 0 + z * g 1 0)))
        * complexTestFun (-P.k₂) (-(t * (y * g 0 1 + z * g 1 1))) * psi (-z))
      = fun z : ℂ => PsiC P g (t * z) (t * y) * psiComplex (t * z * t⁻¹) := by
    funext z
    simp only [PsiC]
    rw [psi_neg_eq_psiComplex, show t * z * t⁻¹ = z by rw [mul_comm t z, mul_inv_cancel_right₀ ht]]
    congr 3 <;> ring
  rw [e, integral_comp_mul_left_C (fun x : ℂ => PsiC P g x (t * y) * psiComplex (x * t⁻¹)) t, Complex.real_smul]
  rfl

end TateComplex.Datum

end

end

section

open Complex MeasureTheory LanglandsTunnell LanglandsTunnell.ArchPlace LanglandsTunnell.Converse.ArchC
p2m_open "TateComplex.W3C P2MW.S_LanglandsTunnell_Converse_exists_archDatumC_W_ne_zero.TateComplex.W3C"

noncomputable section

namespace TateComplex
namespace Datum

private def chg (p : ℂ × ℂ) : ℂ × ℂ := (p.1 * p.2, p.1⁻¹)

private def dom : Set (ℂ × ℂ) := {p | p.1 ≠ 0}

private def tgt : Set (ℂ × ℂ) := {q | q.2 ≠ 0}

private theorem measurableSet_dom : MeasurableSet dom :=
  (measurableSet_singleton (0 : ℂ)).compl.preimage measurable_fst

private theorem chg_image_dom : chg '' dom = tgt := by
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact inv_ne_zero hp
  · intro hq
    refine ⟨(q.2⁻¹, q.2 * q.1), inv_ne_zero hq, ?_⟩
    simp only [chg]
    rw [inv_mul_cancel_left₀ hq, inv_inv]

private theorem chg_injOn : Set.InjOn chg dom := by
  intro p hp q _ h
  simp only [chg, Prod.mk.injEq] at h
  have h1 : p.1 = q.1 := inv_inj.mp h.2
  have h2 : p.2 = q.2 := mul_left_cancel₀ hp (h.1.trans (by rw [h1]))
  exact Prod.ext h1 h2

private def chgDeriv (p : ℂ × ℂ) : ℂ × ℂ →L[ℂ] ℂ × ℂ :=
  (p.2 • ContinuousLinearMap.fst ℂ ℂ ℂ + p.1 • ContinuousLinearMap.snd ℂ ℂ ℂ).prod
    ((-(p.1 ^ 2)⁻¹) • ContinuousLinearMap.fst ℂ ℂ ℂ)

private theorem hasFDerivAt_chg {p : ℂ × ℂ} (hp : p.1 ≠ 0) : HasFDerivAt chg (chgDeriv p) p := by
  have h1 : HasFDerivAt (fun q : ℂ × ℂ => q.1 * q.2)
      (p.2 • ContinuousLinearMap.fst ℂ ℂ ℂ + p.1 • ContinuousLinearMap.snd ℂ ℂ ℂ) p := by
    have := (hasFDerivAt_fst (𝕜 := ℂ) (p := p)).mul (hasFDerivAt_snd (𝕜 := ℂ) (p := p))
    refine this.congr_fderiv ?_
    ext <;> simp
  have h2 : HasFDerivAt (fun q : ℂ × ℂ => q.1⁻¹) ((-(p.1 ^ 2)⁻¹) • ContinuousLinearMap.fst ℂ ℂ ℂ) p := by
    have := (hasDerivAt_inv hp).hasFDerivAt.comp p (hasFDerivAt_fst (𝕜 := ℂ) (p := p))
    refine this.congr_fderiv ?_
    ext <;> simp
  exact h1.prodMk h2

private theorem det_chgDeriv_restrict {p : ℂ × ℂ} (hp : p.1 ≠ 0) :
    ((chgDeriv p).restrictScalars ℝ).det = (‖p.1‖ ^ 2)⁻¹ := by
  have hlin : ((chgDeriv p : ℂ × ℂ →L[ℂ] ℂ × ℂ) : ℂ × ℂ →ₗ[ℂ] ℂ × ℂ)
      = Matrix.toLin (Module.Basis.finTwoProd ℂ) (Module.Basis.finTwoProd ℂ) !![p.2, p.1; -(p.1 ^ 2)⁻¹, 0] := by
    rw [Matrix.toLin_finTwoProd]
    apply LinearMap.ext
    intro v
    simp [chgDeriv]
  have hdet : p.2 * 0 - p.1 * -(p.1 ^ 2)⁻¹ = p.1⁻¹ := by
    field_simp
    ring
  rw [ContinuousLinearMap.det, ContinuousLinearMap.coe_restrictScalars, LinearMap.det_restrictScalars, hlin,
    LinearMap.det_toLin, Matrix.det_fin_two_of, hdet, Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq,
    norm_inv, inv_pow]

variable (P : ComplexArchParam) (g : Matrix (Fin 2) (Fin 2) ℂ) (u s : ℂ) (k : ℤ)

private def normalizer : ℂ := ((‖g.det‖ ^ 2 : ℝ) : ℂ) * quasiChar P.u₁ P.k₁ g.det

private def hatPsi (ξ Y : ℂ) : ℂ := FC (fun x => PsiC P g x Y) ξ

private theorem hatPsi_eq (ξ Y : ℂ) : hatPsi P g ξ Y = W3C.F₁C (PsiC P g) (starRingEnd ℂ ξ) Y := by
  simp only [hatPsi, W3C.F₁C, Complex.conj_conj]

private def zint2 (q : ℂ × ℂ) : ℂ :=
  ((‖q.1 * g.det‖ ^ 2 : ℝ) : ℂ) * quasiChar P.u₁ P.k₁ (q.1 * g.det)
    * (innerWC P (diagOne q.1 * g) q.2 * quasiChar (P.u₁ - P.u₂) (P.k₁ - P.k₂) q.2)
    * (quasiChar u k q.1 * ((‖q.1‖ ^ 2 : ℝ) : ℂ) ^ (s - 1) * (((‖q.1‖ ^ 2 : ℝ) : ℂ))⁻¹)

private theorem zetaIntegrand_eq_integral_zint2 (y : ℂ) :
    zetaIntegrand (WmemC P) g u k s y = ∫ t : ℂ, zint2 P g u s k (y, t) := by
  have e : (∫ t : ℂ, zint2 P g u s k (y, t))
      = (((‖y * g.det‖ ^ 2 : ℝ) : ℂ) * quasiChar P.u₁ P.k₁ (y * g.det)
          * ∫ t : ℂ, innerWC P (diagOne y * g) t * quasiChar (P.u₁ - P.u₂) (P.k₁ - P.k₂) t)
        * (quasiChar u k y * ((‖y‖ ^ 2 : ℝ) : ℂ) ^ (s - 1) * (((‖y‖ ^ 2 : ℝ) : ℂ))⁻¹) := by
    simp only [zint2]
    rw [integral_mul_const, integral_const_mul]
  rw [e]
  unfold zetaIntegrand WmemC
  rw [det_diagOne_mul]
  ring

private theorem key_identity {p : ℂ × ℂ} (h1 : p.1 ≠ 0) (h2 : p.2 ≠ 0) :
    (((‖p.1‖ ^ 2)⁻¹ : ℝ) : ℂ) * zint2 P g u s k (chg p)
      = normalizer P g * zintC (hatPsi P g) (k + P.k₂) (k + P.k₁) (s + u + P.u₂) (s + u + P.u₁) p := by
  have h1i : p.1⁻¹ ≠ 0 := inv_ne_zero h1
  have hinner : innerWC P (diagOne (p.1 * p.2) * g) p.1⁻¹
      = (((‖p.1⁻¹‖ ^ 2)⁻¹ : ℝ) : ℂ) * hatPsi P g p.1 p.2 := by
    rw [innerWC_diagOne_mul P g _ h1i, inv_mul_cancel_left₀ h1, inv_inv, hatPsi]
  have hn : ((‖p.1 * p.2 * g.det‖ ^ 2 : ℝ) : ℂ)
      = ((‖p.1‖ ^ 2 : ℝ) : ℂ) * ((‖p.2‖ ^ 2 : ℝ) : ℂ) * ((‖g.det‖ ^ 2 : ℝ) : ℂ) := by
    rw [norm_mul, norm_mul]; push_cast; ring
  have hpow : ((‖p.1 * p.2‖ ^ 2 : ℝ) : ℂ) ^ (s - 1)
      = ((‖p.1‖ ^ 2 : ℝ) : ℂ) ^ (s - 1) * ((‖p.2‖ ^ 2 : ℝ) : ℂ) ^ (s - 1) := by
    rw [norm_mul, mul_pow, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity)]
  have hinv : (((‖p.1 * p.2‖ ^ 2 : ℝ) : ℂ))⁻¹ = (((‖p.1‖ ^ 2 : ℝ) : ℂ))⁻¹ * (((‖p.2‖ ^ 2 : ℝ) : ℂ))⁻¹ := by
    rw [norm_mul, mul_pow, Complex.ofReal_mul, mul_inv]
  simp only [zint2, chg]
  rw [hinner, hn, hpow, hinv, quasiChar_mul_arg P.u₁ P.k₁ (p.1 * p.2) g.det, quasiChar_mul_arg P.u₁ P.k₁ p.1 p.2,
    quasiChar_mul_arg u k p.1 p.2]
  rw [zintC, normalizer, ← collect_xi P u s k h1, ← collect_Y P u s k h2]
  ring

private theorem ae_mem_dom : ∀ᵐ p : ℂ × ℂ ∂((volume : Measure ℂ).prod volume), p ∈ dom :=
  ae_off_axes_C.mono fun _ hp => hp.1

private theorem ae_mem_tgt : ∀ᵐ q : ℂ × ℂ ∂((volume : Measure ℂ).prod volume), q ∈ tgt :=
  ae_off_axes_C.mono fun _ hq => hq.2

private theorem key_identity_ae :
    (fun p : ℂ × ℂ => |((chgDeriv p).restrictScalars ℝ).det| • zint2 P g u s k (chg p))
      =ᵐ[(volume : Measure ℂ).prod volume]
        fun p => normalizer P g * zintC (hatPsi P g) (k + P.k₂) (k + P.k₁) (s + u + P.u₂) (s + u + P.u₁) p := by
  filter_upwards [ae_off_axes_C] with p hp
  rw [det_chgDeriv_restrict hp.1, abs_of_nonneg (by positivity), Complex.real_smul, key_identity P g u s k hp.1 hp.2]

private theorem zintC_hatPsi_ae :
    (fun p : ℂ × ℂ => zintC (W3C.F₁C (PsiC P g)) (-(k + P.k₂)) (k + P.k₁) (s + u + P.u₂) (s + u + P.u₁)
        (Prod.map (Complex.conjLIE : ℂ → ℂ) id p))
      =ᵐ[(volume : Measure ℂ).prod volume]
        zintC (hatPsi P g) (k + P.k₂) (k + P.k₁) (s + u + P.u₂) (s + u + P.u₁) := by
  filter_upwards [ae_off_axes_C] with p hp
  simp only [zintC, Prod.map_fst, Prod.map_snd, id_eq, Complex.conjLIE_apply, hatPsi_eq]
  rw [kerC_conj hp.1, neg_neg]

private theorem measurePreserving_conj_fst :
    MeasurePreserving (Prod.map (Complex.conjLIE : ℂ → ℂ) (id : ℂ → ℂ)) ((volume : Measure ℂ).prod volume)
      ((volume : Measure ℂ).prod volume) :=
  Complex.conjLIE.measurePreserving.prod (MeasurePreserving.id volume)

private theorem measurableEmbedding_conj_fst : MeasurableEmbedding (Prod.map (Complex.conjLIE : ℂ → ℂ) (id : ℂ → ℂ)) :=
  Complex.conjLIE.toHomeomorph.measurableEmbedding.prodMap MeasurableEmbedding.id

private theorem ZC_hatPsi_eq :
    ZC (hatPsi P g) (k + P.k₂) (k + P.k₁) (s + u + P.u₂) (s + u + P.u₁)
      = ZC (W3C.F₁C (PsiC P g)) (-(k + P.k₂)) (k + P.k₁) (s + u + P.u₂) (s + u + P.u₁) := by
  unfold ZC
  rw [Measure.volume_eq_prod, ← integral_congr_ae (zintC_hatPsi_ae P g u s k),
    measurePreserving_conj_fst.integral_comp measurableEmbedding_conj_fst
      (zintC (W3C.F₁C (PsiC P g)) (-(k + P.k₂)) (k + P.k₁) (s + u + P.u₂) (s + u + P.u₁))]

private theorem integrable_zintC_hatPsi (hg : g.det ≠ 0) (h₁ : 0 < (s + u + P.u₁).re) (h₂ : 0 < (s + u + P.u₂).re) :
    Integrable (zintC (hatPsi P g) (k + P.k₂) (k + P.k₁) (s + u + P.u₂) (s + u + P.u₁))
      ((volume : Measure ℂ).prod volume) := by
  have hZ := (clsC_PsiC P hg).F₁C.integrable_zintC (-(k + P.k₂)) (k + P.k₁) h₂ h₁
  exact ((measurePreserving_conj_fst.integrable_comp_emb measurableEmbedding_conj_fst).mpr hZ).congr
    (zintC_hatPsi_ae P g u s k)

private theorem hasFDerivWithinAt_chg : ∀ p ∈ dom, HasFDerivWithinAt chg ((chgDeriv p).restrictScalars ℝ) dom p :=
  fun _ hp => ((hasFDerivAt_chg hp).restrictScalars ℝ).hasFDerivWithinAt

private theorem integrable_zint2 (hg : g.det ≠ 0) (h₁ : 0 < (s + u + P.u₁).re) (h₂ : 0 < (s + u + P.u₂).re) :
    Integrable (zint2 P g u s k) ((volume : Measure ℂ).prod volume) := by
  have hS : IntegrableOn (zint2 P g u s k) (chg '' dom) ((volume : Measure ℂ).prod volume) := by
    rw [integrableOn_image_iff_integrableOn_abs_det_fderiv_smul _ measurableSet_dom (hasFDerivWithinAt_chg)
      chg_injOn]
    exact ((integrable_zintC_hatPsi P g u s k hg h₁ h₂).const_mul (normalizer P g)).integrableOn.congr_fun_ae
      (ae_restrict_of_ae (key_identity_ae P g u s k).symm)
  rw [chg_image_dom, IntegrableOn, Measure.restrict_eq_self_of_ae_mem ae_mem_tgt] at hS
  exact hS

private theorem integral_zetaIntegrand_WmemC (hg : g.det ≠ 0) (h₁ : 0 < (s + u + P.u₁).re)
    (h₂ : 0 < (s + u + P.u₂).re) :
    ∫ y : ℂ, zetaIntegrand (WmemC P) g u k s y
      = normalizer P g * ZC (W3C.F₁C (PsiC P g)) (-(k + P.k₂)) (k + P.k₁) (s + u + P.u₂) (s + u + P.u₁) := by
  rw [← ZC_hatPsi_eq]
  simp only [zetaIntegrand_eq_integral_zint2]
  rw [← integral_prod _ (integrable_zint2 P g u s k hg h₁ h₂),
    ← Measure.restrict_eq_self_of_ae_mem ae_mem_tgt, ← chg_image_dom,
    integral_image_eq_integral_abs_det_fderiv_smul _ measurableSet_dom hasFDerivWithinAt_chg chg_injOn,
    setIntegral_congr_ae measurableSet_dom ((key_identity_ae P g u s k).mono fun _ h _ => h),
    Measure.restrict_eq_self_of_ae_mem ae_mem_dom, integral_const_mul]
  unfold ZC
  rw [Measure.volume_eq_prod]

end TateComplex.Datum

end

end

section

open Complex ComplexConjugate

noncomputable section

namespace ArchEngineC

local notation "X₄ℂ" => (Fin 2 → Fin 2 → ℂ)

private def coordCLM (i j : Fin 2) : X₄ℂ →L[ℝ] ℂ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℂ) j).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => Fin 2 → ℂ) i)

@[scoped simp] private theorem coordCLM_apply (i j : Fin 2) (e : X₄ℂ) : coordCLM i j e = e i j := by
  simp [coordCLM]

private def conjCoordCLM (i j : Fin 2) : X₄ℂ →L[ℝ] ℂ := (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (coordCLM i j)

@[scoped simp] private theorem conjCoordCLM_apply (i j : Fin 2) (e : X₄ℂ) : conjCoordCLM i j e = conj (e i j) := by
  simp [conjCoordCLM]

private theorem hasFDerivAt_coord (i j : Fin 2) (m : X₄ℂ) : HasFDerivAt (fun m : X₄ℂ => m i j) (coordCLM i j) m :=
  (coordCLM i j).hasFDerivAt.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun e => (coordCLM_apply i j e).symm)

private theorem hasFDerivAt_conjCoord (i j : Fin 2) (m : X₄ℂ) :
    HasFDerivAt (fun m : X₄ℂ => conj (m i j)) (conjCoordCLM i j) m :=
  (conjCoordCLM i j).hasFDerivAt.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun e => (conjCoordCLM_apply i j e).symm)

private def sumForm (c c' : Fin 2 → Fin 2 → ℂ) : X₄ℂ →L[ℝ] ℂ :=
  ∑ i : Fin 2, ∑ j : Fin 2, (c i j • coordCLM i j + c' i j • conjCoordCLM i j)

private theorem sumForm_apply (c c' : Fin 2 → Fin 2 → ℂ) (v : X₄ℂ) :
    sumForm c c' v = ∑ i : Fin 2, ∑ j : Fin 2, (c i j * v i j + c' i j * conj (v i j)) := by
  simp [sumForm]

private def wirt (a b : ℂ) : ℂ →L[ℝ] ℂ := a • ContinuousLinearMap.id ℝ ℂ + b • (Complex.conjCLE : ℂ →L[ℝ] ℂ)

private theorem wirt_apply (a b v : ℂ) : wirt a b v = a * v + b * conj v := by
  simp [wirt]

private inductive IsPoly : (X₄ℂ → ℂ → ℂ → ℂ) → Prop
  | const (c : ℂ) : IsPoly fun _ _ _ => c
  | rowOne (j : Fin 2) : IsPoly fun m _ _ => m 1 j
  | rowOneBar (j : Fin 2) : IsPoly fun m _ _ => conj (m 1 j)
  | rowZeroY (j : Fin 2) : IsPoly fun m _ Y => Y * m 0 j
  | rowZeroYBar (j : Fin 2) : IsPoly fun m _ Y => conj Y * conj (m 0 j)
  | varX : IsPoly fun _ x _ => x
  | varXBar : IsPoly fun _ x _ => conj x
  | varY : IsPoly fun _ _ Y => Y
  | varYBar : IsPoly fun _ _ Y => conj Y
  | add {P Q : X₄ℂ → ℂ → ℂ → ℂ} (hP : IsPoly P) (hQ : IsPoly Q) : IsPoly fun m x Y => P m x Y + Q m x Y
  | mul {P Q : X₄ℂ → ℂ → ℂ → ℂ} (hP : IsPoly P) (hQ : IsPoly Q) : IsPoly fun m x Y => P m x Y * Q m x Y

namespace IsPoly

private theorem congr {P Q : X₄ℂ → ℂ → ℂ → ℂ} (h : IsPoly P) (e : P = Q) : IsPoly Q := e ▸ h

private theorem smul {P : X₄ℂ → ℂ → ℂ → ℂ} (h : IsPoly P) (c : ℂ) : IsPoly fun m x Y => c * P m x Y :=
  (const c).mul h

private theorem neg {P : X₄ℂ → ℂ → ℂ → ℂ} (h : IsPoly P) : IsPoly fun m x Y => -P m x Y :=
  (h.smul (-1)).congr (by funext m x Y; ring)

private theorem sub {P Q : X₄ℂ → ℂ → ℂ → ℂ} (hP : IsPoly P) (hQ : IsPoly Q) :
    IsPoly fun m x Y => P m x Y - Q m x Y :=
  (hP.add hQ.neg).congr (by funext m x Y; ring)

private theorem conj_mem {P : X₄ℂ → ℂ → ℂ → ℂ} (h : IsPoly P) : IsPoly fun m x Y => conj (P m x Y) := by
  induction h with
  | const c => exact const (conj c)
  | rowOne j => exact rowOneBar j
  | rowOneBar j =>
    refine (rowOne j).congr ?_
    funext m x Y
    simp
  | rowZeroY j =>
    refine (rowZeroYBar j).congr ?_
    funext m x Y
    simp
  | rowZeroYBar j =>
    refine (rowZeroY j).congr ?_
    funext m x Y
    simp
  | varX => exact varXBar
  | varXBar =>
    refine varX.congr ?_
    funext m x Y
    simp
  | varY => exact varYBar
  | varYBar =>
    refine varY.congr ?_
    funext m x Y
    simp
  | add _ _ ihP ihQ =>
    refine (ihP.add ihQ).congr ?_
    funext m x Y
    simp
  | mul _ _ ihP ihQ =>
    refine (ihP.mul ihQ).congr ?_
    funext m x Y
    simp

private theorem
    linForm (j : Fin 2) : IsPoly fun m x Y => Y * m 0 j + x * m 1 j := (rowZeroY j).add (varX.mul (rowOne j))

private theorem contDiff_x {P : X₄ℂ → ℂ → ℂ → ℂ} (h : IsPoly P) (m : X₄ℂ) (Y : ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) fun x : ℂ => P m x Y := by
  induction h with
  | const c => exact contDiff_const
  | rowOne j => exact contDiff_const
  | rowOneBar j => exact contDiff_const
  | rowZeroY j => exact contDiff_const
  | rowZeroYBar j => exact contDiff_const
  | varX =>
    show ContDiff ℝ (⊤ : ℕ∞) (id : ℂ → ℂ)
    exact contDiff_id
  | varXBar =>
    have e : (fun x : ℂ => conj x) = ⇑Complex.conjCLE := by
      funext x
      rw [Complex.conjCLE_apply]
    show ContDiff ℝ (⊤ : ℕ∞) fun x : ℂ => conj x
    rw [e]
    exact Complex.conjCLE.contDiff
  | varY => exact contDiff_const
  | varYBar => exact contDiff_const
  | add _ _ ihP ihQ => exact ihP.add ihQ
  | mul _ _ ihP ihQ => exact ihP.mul ihQ

private theorem hasFDerivAt_x {P : X₄ℂ → ℂ → ℂ → ℂ} (h : IsPoly P) :
    ∃ P₁ P₂ : X₄ℂ → ℂ → ℂ → ℂ, IsPoly P₁ ∧ IsPoly P₂ ∧
      ∀ (m : X₄ℂ) (x Y : ℂ), HasFDerivAt (fun x => P m x Y) (wirt (P₁ m x Y) (P₂ m x Y)) x := by
  have hzero : wirt 0 0 = 0 := by
    refine ContinuousLinearMap.ext fun v => ?_
    rw [wirt_apply]
    simp
  have hconst : ∀ (c x : ℂ), HasFDerivAt (fun (_ : ℂ) => c) (wirt 0 0) x := by
    intro c x
    rw [hzero]
    exact hasFDerivAt_const c x
  induction h with
  | const c => exact ⟨fun _ _ _ => 0, fun _ _ _ => 0, const 0, const 0, fun m x Y => hconst c x⟩
  | rowOne j => exact ⟨fun _ _ _ => 0, fun _ _ _ => 0, const 0, const 0, fun m x Y => hconst (m 1 j) x⟩
  | rowOneBar j => exact ⟨fun _ _ _ => 0, fun _ _ _ => 0, const 0, const 0, fun m x Y => hconst (conj (m 1 j)) x⟩
  | rowZeroY j => exact ⟨fun _ _ _ => 0, fun _ _ _ => 0, const 0, const 0, fun m x Y => hconst (Y * m 0 j) x⟩
  | rowZeroYBar j =>
    exact ⟨fun _ _ _ => 0, fun _ _ _ => 0, const 0, const 0, fun m x Y => hconst (conj Y * conj (m 0 j)) x⟩
  | varX =>
    refine ⟨fun _ _ _ => 1, fun _ _ _ => 0, const 1, const 0, fun m x Y => ?_⟩
    refine (hasFDerivAt_id x).congr_fderiv ?_
    refine ContinuousLinearMap.ext fun v => ?_
    rw [wirt_apply]
    simp
  | varXBar =>
    refine ⟨fun _ _ _ => 0, fun _ _ _ => 1, const 0, const 1, fun m x Y => ?_⟩
    have h1 : HasFDerivAt (fun x : ℂ => conj x) (Complex.conjCLE : ℂ →L[ℝ] ℂ) x :=
      Complex.conjCLE.hasFDerivAt.congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun z => (Complex.conjCLE_apply z).symm)
    refine h1.congr_fderiv ?_
    refine ContinuousLinearMap.ext fun v => ?_
    rw [wirt_apply]
    simp
  | varY => exact ⟨fun _ _ _ => 0, fun _ _ _ => 0, const 0, const 0, fun m x Y => hconst Y x⟩
  | varYBar => exact ⟨fun _ _ _ => 0, fun _ _ _ => 0, const 0, const 0, fun m x Y => hconst (conj Y) x⟩
  | @add P Q _ _ ihP ihQ =>
    obtain ⟨P₁, P₂, hP₁, hP₂, hdP⟩ := ihP
    obtain ⟨Q₁, Q₂, hQ₁, hQ₂, hdQ⟩ := ihQ
    refine ⟨fun m x Y => P₁ m x Y + Q₁ m x Y, fun m x Y => P₂ m x Y + Q₂ m x Y, hP₁.add hQ₁, hP₂.add hQ₂,
      fun m x Y => ?_⟩
    refine ((hdP m x Y).add (hdQ m x Y)).congr_fderiv ?_
    refine ContinuousLinearMap.ext fun v => ?_
    simp only [ContinuousLinearMap.add_apply, wirt_apply]
    ring
  | @mul P Q hP hQ ihP ihQ =>
    obtain ⟨P₁, P₂, hP₁, hP₂, hdP⟩ := ihP
    obtain ⟨Q₁, Q₂, hQ₁, hQ₂, hdQ⟩ := ihQ
    refine ⟨fun m x Y => P m x Y * Q₁ m x Y + Q m x Y * P₁ m x Y,
      fun m x Y => P m x Y * Q₂ m x Y + Q m x Y * P₂ m x Y,
      (hP.mul hQ₁).add (hQ.mul hP₁), (hP.mul hQ₂).add (hQ.mul hP₂), fun m x Y => ?_⟩
    refine ((hdP m x Y).mul (hdQ m x Y)).congr_fderiv ?_
    refine ContinuousLinearMap.ext fun v => ?_
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, wirt_apply, smul_eq_mul]
    ring

private theorem hasFDerivAt_m {P : X₄ℂ → ℂ → ℂ → ℂ} (h : IsPoly P) :
    ∃ D D' : Fin 2 → Fin 2 → X₄ℂ → ℂ → ℂ → ℂ, (∀ i j, IsPoly (D i j)) ∧ (∀ i j, IsPoly (D' i j)) ∧
      ∀ (m : X₄ℂ) (x Y : ℂ),
        HasFDerivAt (fun m => P m x Y) (sumForm (fun i j => D i j m x Y) (fun i j => D' i j m x Y)) m := by
  have hzero : sumForm (fun _ _ => (0 : ℂ)) (fun _ _ => (0 : ℂ)) = 0 := by
    refine ContinuousLinearMap.ext fun v => ?_
    rw [sumForm_apply]
    simp
  have hconst : ∀ (c : ℂ) (m : X₄ℂ),
      HasFDerivAt (fun (_ : X₄ℂ) => c) (sumForm (fun _ _ => (0 : ℂ)) (fun _ _ => (0 : ℂ))) m := by
    intro c m
    rw [hzero]
    exact hasFDerivAt_const c m
  induction h with
  | const c =>
    exact ⟨fun _ _ _ _ _ => 0, fun _ _ _ _ _ => 0, fun _ _ => const 0, fun _ _ => const 0, fun m x Y => hconst c m⟩
  | rowOne j₀ =>
    refine ⟨fun i j _ _ _ => if i = 1 ∧ j = j₀ then (1 : ℂ) else 0, fun _ _ _ _ _ => 0, fun i j => ?_,
      fun _ _ => const 0, fun m x Y => ?_⟩
    · by_cases hc : i = 1 ∧ j = j₀
      · simp only [hc, and_self, if_true]
        exact const 1
      · simp only [hc, if_false]
        exact const 0
    · refine (hasFDerivAt_coord 1 j₀ m).congr_fderiv ?_
      refine ContinuousLinearMap.ext fun v => ?_
      fin_cases j₀ <;> simp [sumForm_apply, Fin.sum_univ_two]
  | rowOneBar j₀ =>
    refine ⟨fun _ _ _ _ _ => 0, fun i j _ _ _ => if i = 1 ∧ j = j₀ then (1 : ℂ) else 0, fun _ _ => const 0,
      fun i j => ?_, fun m x Y => ?_⟩
    · by_cases hc : i = 1 ∧ j = j₀
      · simp only [hc, and_self, if_true]
        exact const 1
      · simp only [hc, if_false]
        exact const 0
    · refine (hasFDerivAt_conjCoord 1 j₀ m).congr_fderiv ?_
      refine ContinuousLinearMap.ext fun v => ?_
      fin_cases j₀ <;> simp [sumForm_apply, Fin.sum_univ_two]
  | rowZeroY j₀ =>
    refine ⟨fun i j _ _ Y => if i = 0 ∧ j = j₀ then Y else 0, fun _ _ _ _ _ => 0, fun i j => ?_,
      fun _ _ => const 0, fun m x Y => ?_⟩
    · by_cases hc : i = 0 ∧ j = j₀
      · simp only [hc, and_self, if_true]
        exact varY
      · simp only [hc, if_false]
        exact const 0
    · refine ((hasFDerivAt_coord 0 j₀ m).const_mul Y).congr_fderiv ?_
      refine ContinuousLinearMap.ext fun v => ?_
      fin_cases j₀ <;> simp [sumForm_apply, Fin.sum_univ_two]
  | rowZeroYBar j₀ =>
    refine ⟨fun _ _ _ _ _ => 0, fun i j _ _ Y => if i = 0 ∧ j = j₀ then conj Y else 0, fun _ _ => const 0,
      fun i j => ?_, fun m x Y => ?_⟩
    · by_cases hc : i = 0 ∧ j = j₀
      · simp only [hc, and_self, if_true]
        exact varYBar
      · simp only [hc, if_false]
        exact const 0
    · refine ((hasFDerivAt_conjCoord 0 j₀ m).const_mul (conj Y)).congr_fderiv ?_
      refine ContinuousLinearMap.ext fun v => ?_
      fin_cases j₀ <;> simp [sumForm_apply, Fin.sum_univ_two]
  | varX =>
    exact ⟨fun _ _ _ _ _ => 0, fun _ _ _ _ _ => 0, fun _ _ => const 0, fun _ _ => const 0,
      fun m x Y => hconst x m⟩
  | varXBar =>
    exact ⟨fun _ _ _ _ _ => 0, fun _ _ _ _ _ => 0, fun _ _ => const 0, fun _ _ => const 0,
      fun m x Y => hconst (conj x) m⟩
  | varY =>
    exact ⟨fun _ _ _ _ _ => 0, fun _ _ _ _ _ => 0, fun _ _ => const 0, fun _ _ => const 0,
      fun m x Y => hconst Y m⟩
  | varYBar =>
    exact ⟨fun _ _ _ _ _ => 0, fun _ _ _ _ _ => 0, fun _ _ => const 0, fun _ _ => const 0,
      fun m x Y => hconst (conj Y) m⟩
  | @add P Q _ _ ihP ihQ =>
    obtain ⟨D₁, D₁', hD₁, hD₁', hd₁⟩ := ihP
    obtain ⟨D₂, D₂', hD₂, hD₂', hd₂⟩ := ihQ
    refine ⟨fun i j m x Y => D₁ i j m x Y + D₂ i j m x Y, fun i j m x Y => D₁' i j m x Y + D₂' i j m x Y,
      fun i j => (hD₁ i j).add (hD₂ i j), fun i j => (hD₁' i j).add (hD₂' i j), fun m x Y => ?_⟩
    refine ((hd₁ m x Y).add (hd₂ m x Y)).congr_fderiv ?_
    refine ContinuousLinearMap.ext fun v => ?_
    simp only [ContinuousLinearMap.add_apply, sumForm_apply, Fin.sum_univ_two]
    ring
  | @mul P Q hP hQ ihP ihQ =>
    obtain ⟨D₁, D₁', hD₁, hD₁', hd₁⟩ := ihP
    obtain ⟨D₂, D₂', hD₂, hD₂', hd₂⟩ := ihQ
    refine ⟨fun i j m x Y => P m x Y * D₂ i j m x Y + Q m x Y * D₁ i j m x Y,
      fun i j m x Y => P m x Y * D₂' i j m x Y + Q m x Y * D₁' i j m x Y,
      fun i j => (hP.mul (hD₂ i j)).add (hQ.mul (hD₁ i j)),
      fun i j => (hP.mul (hD₂' i j)).add (hQ.mul (hD₁' i j)), fun m x Y => ?_⟩
    refine ((hd₁ m x Y).mul (hd₂ m x Y)).congr_fderiv ?_
    refine ContinuousLinearMap.ext fun v => ?_
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, sumForm_apply, Fin.sum_univ_two,
      smul_eq_mul]
    ring

private theorem differentiable_m {P : X₄ℂ → ℂ → ℂ → ℂ} (h : IsPoly P) (x Y : ℂ) :
    Differentiable ℝ fun m : X₄ℂ => P m x Y := by
  obtain ⟨D, D', -, -, hd⟩ := h.hasFDerivAt_m
  exact fun m => (hd m x Y).differentiableAt

end IsPoly

private def qForm (m : X₄ℂ) (x Y : ℂ) : ℝ := ‖Y * m 0 0 + x * m 1 0‖ ^ 2 + ‖Y * m 0 1 + x * m 1 1‖ ^ 2

private theorem qForm_nonneg (m : X₄ℂ) (x Y : ℂ) : 0 ≤ qForm m x Y := by
  unfold qForm
  positivity

private def expo (m : X₄ℂ) (x Y : ℂ) : ℂ :=
  -(2 * (Real.pi : ℂ)) *
    ((Y * m 0 0 + x * m 1 0) * conj (Y * m 0 0 + x * m 1 0) + (Y * m 0 1 + x * m 1 1) * conj (Y * m 0 1 + x * m 1 1))

private theorem isPoly_expo : IsPoly expo := by
  have h : IsPoly fun m x Y => -(2 * (Real.pi : ℂ)) *
      ((Y * m 0 0 + x * m 1 0) * conj (Y * m 0 0 + x * m 1 0) +
        (Y * m 0 1 + x * m 1 1) * conj (Y * m 0 1 + x * m 1 1)) :=
    (((IsPoly.linForm 0).mul (IsPoly.linForm 0).conj_mem).add
      ((IsPoly.linForm 1).mul (IsPoly.linForm 1).conj_mem)).smul _
  exact h

private theorem expo_eq (m : X₄ℂ) (x Y : ℂ) : expo m x Y = ((-(2 * Real.pi) * qForm m x Y : ℝ) : ℂ) := by
  simp only [expo, qForm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  ring

private theorem expo_re (m : X₄ℂ) (x Y : ℂ) : (expo m x Y).re = -(2 * Real.pi) * qForm m x Y := by
  rw [expo_eq, Complex.ofReal_re]

private def gaussW (m : X₄ℂ) (x Y : ℂ) : ℂ := Complex.exp (expo m x Y)

private theorem norm_gaussW (m : X₄ℂ) (x Y : ℂ) : ‖gaussW m x Y‖ = Real.exp (-(2 * Real.pi) * qForm m x Y) := by
  rw [gaussW, Complex.norm_exp, expo_re]

private theorem gaussW_ne_zero (m : X₄ℂ) (x Y : ℂ) : gaussW m x Y ≠ 0 := Complex.exp_ne_zero _

private def phiFam (P : X₄ℂ → ℂ → ℂ → ℂ) (m : X₄ℂ) (x Y : ℂ) : ℂ := P m x Y * gaussW m x Y

namespace IsPoly

private theorem contDiff_x_phiFam {P : X₄ℂ → ℂ → ℂ → ℂ} (h : IsPoly P) (m : X₄ℂ) (Y : ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) fun x : ℂ => phiFam P m x Y := by
  have hE := isPoly_expo.contDiff_x m Y
  have hg : ContDiff ℝ (⊤ : ℕ∞) fun x : ℂ => gaussW m x Y := Complex.contDiff_exp.comp hE
  exact (h.contDiff_x m Y).mul hg

private theorem hasFDerivAt_x_phiFam {P : X₄ℂ → ℂ → ℂ → ℂ} (h : IsPoly P) :
    ∃ P₁ P₂ : X₄ℂ → ℂ → ℂ → ℂ, IsPoly P₁ ∧ IsPoly P₂ ∧
      ∀ (m : X₄ℂ) (x Y : ℂ),
        HasFDerivAt (fun x => phiFam P m x Y) (wirt (phiFam P₁ m x Y) (phiFam P₂ m x Y)) x := by
  obtain ⟨P₁, P₂, hP₁, hP₂, hdP⟩ := h.hasFDerivAt_x
  obtain ⟨E₁, E₂, hE₁, hE₂, hdE⟩ := isPoly_expo.hasFDerivAt_x
  refine ⟨fun m x Y => P₁ m x Y + P m x Y * E₁ m x Y, fun m x Y => P₂ m x Y + P m x Y * E₂ m x Y,
    hP₁.add (h.mul hE₁), hP₂.add (h.mul hE₂), fun m x Y => ?_⟩
  have hg : HasFDerivAt (fun x => gaussW m x Y) (gaussW m x Y • wirt (E₁ m x Y) (E₂ m x Y)) x :=
    (hdE m x Y).cexp
  show HasFDerivAt (fun x => P m x Y * gaussW m x Y) _ x
  refine ((hdP m x Y).mul hg).congr_fderiv ?_
  refine ContinuousLinearMap.ext fun v => ?_
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, wirt_apply, smul_eq_mul, phiFam]
  ring

private theorem hasFDerivAt_m_phiFam {P : X₄ℂ → ℂ → ℂ → ℂ} (h : IsPoly P) :
    ∃ D D' : Fin 2 → Fin 2 → X₄ℂ → ℂ → ℂ → ℂ, (∀ i j, IsPoly (D i j)) ∧ (∀ i j, IsPoly (D' i j)) ∧
      ∀ (m : X₄ℂ) (x Y : ℂ),
        HasFDerivAt (fun m => phiFam P m x Y)
          (sumForm (fun i j => phiFam (D i j) m x Y) (fun i j => phiFam (D' i j) m x Y)) m := by
  obtain ⟨DP, DP', hDP, hDP', hdP⟩ := h.hasFDerivAt_m
  obtain ⟨DE, DE', hDE, hDE', hdE⟩ := isPoly_expo.hasFDerivAt_m
  refine ⟨fun i j m x Y => DP i j m x Y + P m x Y * DE i j m x Y,
    fun i j m x Y => DP' i j m x Y + P m x Y * DE' i j m x Y,
    fun i j => (hDP i j).add (h.mul (hDE i j)), fun i j => (hDP' i j).add (h.mul (hDE' i j)), fun m x Y => ?_⟩
  have hg : HasFDerivAt (fun m => gaussW m x Y)
      (gaussW m x Y • sumForm (fun i j => DE i j m x Y) (fun i j => DE' i j m x Y)) m :=
    (hdE m x Y).cexp
  show HasFDerivAt (fun m => P m x Y * gaussW m x Y) _ m
  refine ((hdP m x Y).mul hg).congr_fderiv ?_
  refine ContinuousLinearMap.ext fun v => ?_
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, sumForm_apply, Fin.sum_univ_two,
    smul_eq_mul, phiFam]
  ring

end IsPoly

private inductive IsEntryPoly : (X₄ℂ → ℂ) → Prop
  | const (c : ℂ) : IsEntryPoly fun _ => c
  | entry (i j : Fin 2) : IsEntryPoly fun m => m i j
  | entryBar (i j : Fin 2) : IsEntryPoly fun m => conj (m i j)
  | add {R S : X₄ℂ → ℂ} (hR : IsEntryPoly R) (hS : IsEntryPoly S) : IsEntryPoly fun m => R m + S m
  | mul {R S : X₄ℂ → ℂ} (hR : IsEntryPoly R) (hS : IsEntryPoly S) : IsEntryPoly fun m => R m * S m

namespace IsEntryPoly

private theorem congr {R S : X₄ℂ → ℂ} (h : IsEntryPoly R) (e : R = S) : IsEntryPoly S := e ▸ h

private theorem smul {R : X₄ℂ → ℂ} (h : IsEntryPoly R) (c : ℂ) : IsEntryPoly fun m => c * R m := (const c).mul h

private theorem neg {R : X₄ℂ → ℂ} (h : IsEntryPoly R) : IsEntryPoly fun m => -R m :=
  (h.smul (-1)).congr (by funext m; ring)

private theorem sub {R S : X₄ℂ → ℂ} (hR : IsEntryPoly R) (hS : IsEntryPoly S) : IsEntryPoly fun m => R m - S m :=
  (hR.add hS.neg).congr (by funext m; ring)

private theorem conj_mem {R : X₄ℂ → ℂ} (h : IsEntryPoly R) : IsEntryPoly fun m => conj (R m) := by
  induction h with
  | const c => exact const (conj c)
  | entry i j => exact entryBar i j
  | entryBar i j =>
    refine (entry i j).congr ?_
    funext m
    simp
  | add _ _ ihR ihS =>
    refine (ihR.add ihS).congr ?_
    funext m
    simp
  | mul _ _ ihR ihS =>
    refine (ihR.mul ihS).congr ?_
    funext m
    simp

private theorem pow {R : X₄ℂ → ℂ} (h : IsEntryPoly R) (n : ℕ) : IsEntryPoly fun m => R m ^ n := by
  induction n with
  | zero =>
    refine (const 1).congr ?_
    funext m
    simp
  | succ n ih =>
    refine (ih.mul h).congr ?_
    funext m
    simp [pow_succ]

private theorem detCoords : IsEntryPoly fun m : X₄ℂ => m 0 0 * m 1 1 - m 0 1 * m 1 0 :=
  ((entry 0 0).mul (entry 1 1)).sub ((entry 0 1).mul (entry 1 0))

private theorem detCoords_eq (m : X₄ℂ) : m 0 0 * m 1 1 - m 0 1 * m 1 0 = (Matrix.of m).det := by
  rw [Matrix.det_fin_two]
  rfl

private theorem hasFDerivAt {R : X₄ℂ → ℂ} (h : IsEntryPoly R) :
    ∃ D D' : Fin 2 → Fin 2 → X₄ℂ → ℂ, (∀ i j, IsEntryPoly (D i j)) ∧ (∀ i j, IsEntryPoly (D' i j)) ∧
      ∀ m : X₄ℂ, HasFDerivAt R (sumForm (fun i j => D i j m) (fun i j => D' i j m)) m := by
  have hzero : sumForm (fun _ _ => (0 : ℂ)) (fun _ _ => (0 : ℂ)) = 0 := by
    refine ContinuousLinearMap.ext fun v => ?_
    rw [sumForm_apply]
    simp
  induction h with
  | const c =>
    refine ⟨fun _ _ _ => 0, fun _ _ _ => 0, fun _ _ => const 0, fun _ _ => const 0, fun m => ?_⟩
    show HasFDerivAt (fun _ : X₄ℂ => c) (sumForm (fun _ _ => (0 : ℂ)) (fun _ _ => (0 : ℂ))) m
    rw [hzero]
    exact hasFDerivAt_const c m
  | entry i₀ j₀ =>
    refine ⟨fun i j _ => if i = i₀ ∧ j = j₀ then (1 : ℂ) else 0, fun _ _ _ => 0, fun i j => ?_, fun _ _ => const 0,
      fun m => ?_⟩
    · by_cases hc : i = i₀ ∧ j = j₀
      · simp only [hc, and_self, if_true]
        exact const 1
      · simp only [hc, if_false]
        exact const 0
    · refine (hasFDerivAt_coord i₀ j₀ m).congr_fderiv ?_
      refine ContinuousLinearMap.ext fun v => ?_
      fin_cases i₀ <;> fin_cases j₀ <;> simp [sumForm_apply, Fin.sum_univ_two]
  | entryBar i₀ j₀ =>
    refine ⟨fun _ _ _ => 0, fun i j _ => if i = i₀ ∧ j = j₀ then (1 : ℂ) else 0, fun _ _ => const 0, fun i j => ?_,
      fun m => ?_⟩
    · by_cases hc : i = i₀ ∧ j = j₀
      · simp only [hc, and_self, if_true]
        exact const 1
      · simp only [hc, if_false]
        exact const 0
    · refine (hasFDerivAt_conjCoord i₀ j₀ m).congr_fderiv ?_
      refine ContinuousLinearMap.ext fun v => ?_
      fin_cases i₀ <;> fin_cases j₀ <;> simp [sumForm_apply, Fin.sum_univ_two]
  | @add R S _ _ ihR ihS =>
    obtain ⟨D₁, D₁', hD₁, hD₁', hd₁⟩ := ihR
    obtain ⟨D₂, D₂', hD₂, hD₂', hd₂⟩ := ihS
    refine ⟨fun i j m => D₁ i j m + D₂ i j m, fun i j m => D₁' i j m + D₂' i j m,
      fun i j => (hD₁ i j).add (hD₂ i j), fun i j => (hD₁' i j).add (hD₂' i j), fun m => ?_⟩
    refine ((hd₁ m).add (hd₂ m)).congr_fderiv ?_
    refine ContinuousLinearMap.ext fun v => ?_
    simp only [ContinuousLinearMap.add_apply, sumForm_apply, Fin.sum_univ_two]
    ring
  | @mul R S hR hS ihR ihS =>
    obtain ⟨D₁, D₁', hD₁, hD₁', hd₁⟩ := ihR
    obtain ⟨D₂, D₂', hD₂, hD₂', hd₂⟩ := ihS
    refine ⟨fun i j m => R m * D₂ i j m + S m * D₁ i j m, fun i j m => R m * D₂' i j m + S m * D₁' i j m,
      fun i j => (hR.mul (hD₂ i j)).add (hS.mul (hD₁ i j)),
      fun i j => (hR.mul (hD₂' i j)).add (hS.mul (hD₁' i j)), fun m => ?_⟩
    refine ((hd₁ m).mul (hd₂ m)).congr_fderiv ?_
    refine ContinuousLinearMap.ext fun v => ?_
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, sumForm_apply, Fin.sum_univ_two,
      smul_eq_mul]
    ring

private theorem differentiable {R : X₄ℂ → ℂ} (h : IsEntryPoly R) : Differentiable ℝ R := by
  obtain ⟨D, D', -, -, hd⟩ := h.hasFDerivAt
  exact fun m => (hd m).differentiableAt

end IsEntryPoly

namespace IsPoly

private theorem norm_le_of_gen_le {P : X₄ℂ → ℂ → ℂ → ℂ} (h : IsPoly P) :
    ∃ (C : ℝ) (d : ℕ), 0 ≤ C ∧ ∀ (m : X₄ℂ) (x Y : ℂ) (B : ℝ), 1 ≤ B → (∀ j, ‖m 1 j‖ ≤ B) →
      (∀ j, ‖Y * m 0 j‖ ≤ B) → ‖x‖ ≤ B → ‖Y‖ ≤ B → ‖P m x Y‖ ≤ C * B ^ d := by
  induction h with
  | const c => exact ⟨‖c‖, 0, norm_nonneg c, fun m x Y B _ _ _ _ _ => by simp⟩
  | rowOne j =>
    refine ⟨1, 1, zero_le_one, fun m x Y B _ h1 _ _ _ => ?_⟩
    simpa using h1 j
  | rowOneBar j =>
    refine ⟨1, 1, zero_le_one, fun m x Y B _ h1 _ _ _ => ?_⟩
    simpa [Complex.norm_conj] using h1 j
  | rowZeroY j =>
    refine ⟨1, 1, zero_le_one, fun m x Y B _ _ h0 _ _ => ?_⟩
    simpa using h0 j
  | rowZeroYBar j =>
    refine ⟨1, 1, zero_le_one, fun m x Y B _ _ h0 _ _ => ?_⟩
    have h := h0 j
    rw [norm_mul] at h
    simpa [norm_mul, Complex.norm_conj] using h
  | varX =>
    refine ⟨1, 1, zero_le_one, fun m x Y B _ _ _ hx _ => ?_⟩
    simpa using hx
  | varXBar =>
    refine ⟨1, 1, zero_le_one, fun m x Y B _ _ _ hx _ => ?_⟩
    simpa [Complex.norm_conj] using hx
  | varY =>
    refine ⟨1, 1, zero_le_one, fun m x Y B _ _ _ _ hY => ?_⟩
    simpa using hY
  | varYBar =>
    refine ⟨1, 1, zero_le_one, fun m x Y B _ _ _ _ hY => ?_⟩
    simpa [Complex.norm_conj] using hY
  | @add P Q _ _ ihP ihQ =>
    obtain ⟨C₁, d₁, hC₁, h₁⟩ := ihP
    obtain ⟨C₂, d₂, hC₂, h₂⟩ := ihQ
    refine ⟨C₁ + C₂, max d₁ d₂, add_nonneg hC₁ hC₂, fun m x Y B hB h1 h0 hx hY => ?_⟩
    have e₁ := h₁ m x Y B hB h1 h0 hx hY
    have e₂ := h₂ m x Y B hB h1 h0 hx hY
    have p₁ : B ^ d₁ ≤ B ^ max d₁ d₂ := pow_le_pow_right₀ hB (le_max_left _ _)
    have p₂ : B ^ d₂ ≤ B ^ max d₁ d₂ := pow_le_pow_right₀ hB (le_max_right _ _)
    calc ‖P m x Y + Q m x Y‖ ≤ ‖P m x Y‖ + ‖Q m x Y‖ := norm_add_le _ _
      _ ≤ C₁ * B ^ max d₁ d₂ + C₂ * B ^ max d₁ d₂ :=
          add_le_add (e₁.trans (mul_le_mul_of_nonneg_left p₁ hC₁)) (e₂.trans (mul_le_mul_of_nonneg_left p₂ hC₂))
      _ = (C₁ + C₂) * B ^ max d₁ d₂ := by ring
  | @mul P Q _ _ ihP ihQ =>
    obtain ⟨C₁, d₁, hC₁, h₁⟩ := ihP
    obtain ⟨C₂, d₂, hC₂, h₂⟩ := ihQ
    refine ⟨C₁ * C₂, d₁ + d₂, mul_nonneg hC₁ hC₂, fun m x Y B hB h1 h0 hx hY => ?_⟩
    have e₁ := h₁ m x Y B hB h1 h0 hx hY
    have e₂ := h₂ m x Y B hB h1 h0 hx hY
    have hB0 : 0 ≤ B := zero_le_one.trans hB
    calc ‖P m x Y * Q m x Y‖ = ‖P m x Y‖ * ‖Q m x Y‖ := norm_mul _ _
      _ ≤ (C₁ * B ^ d₁) * (C₂ * B ^ d₂) := mul_le_mul e₁ e₂ (norm_nonneg _) (by positivity)
      _ = C₁ * C₂ * B ^ (d₁ + d₂) := by ring

end IsPoly

namespace IsEntryPoly

private theorem norm_le_of_entries_le {R : X₄ℂ → ℂ} (h : IsEntryPoly R) :
    ∃ (C : ℝ) (d : ℕ), 0 ≤ C ∧ ∀ (m : X₄ℂ) (B : ℝ), 1 ≤ B → (∀ i j, ‖m i j‖ ≤ B) → ‖R m‖ ≤ C * B ^ d := by
  induction h with
  | const c => exact ⟨‖c‖, 0, norm_nonneg c, fun m B _ _ => by simp⟩
  | entry i j =>
    refine ⟨1, 1, zero_le_one, fun m B _ hm => ?_⟩
    simpa using hm i j
  | entryBar i j =>
    refine ⟨1, 1, zero_le_one, fun m B _ hm => ?_⟩
    simpa [Complex.norm_conj] using hm i j
  | @add R S _ _ ihR ihS =>
    obtain ⟨C₁, d₁, hC₁, h₁⟩ := ihR
    obtain ⟨C₂, d₂, hC₂, h₂⟩ := ihS
    refine ⟨C₁ + C₂, max d₁ d₂, add_nonneg hC₁ hC₂, fun m B hB hm => ?_⟩
    have e₁ := h₁ m B hB hm
    have e₂ := h₂ m B hB hm
    have p₁ : B ^ d₁ ≤ B ^ max d₁ d₂ := pow_le_pow_right₀ hB (le_max_left _ _)
    have p₂ : B ^ d₂ ≤ B ^ max d₁ d₂ := pow_le_pow_right₀ hB (le_max_right _ _)
    calc ‖R m + S m‖ ≤ ‖R m‖ + ‖S m‖ := norm_add_le _ _
      _ ≤ C₁ * B ^ max d₁ d₂ + C₂ * B ^ max d₁ d₂ :=
          add_le_add (e₁.trans (mul_le_mul_of_nonneg_left p₁ hC₁)) (e₂.trans (mul_le_mul_of_nonneg_left p₂ hC₂))
      _ = (C₁ + C₂) * B ^ max d₁ d₂ := by ring
  | @mul R S _ _ ihR ihS =>
    obtain ⟨C₁, d₁, hC₁, h₁⟩ := ihR
    obtain ⟨C₂, d₂, hC₂, h₂⟩ := ihS
    refine ⟨C₁ * C₂, d₁ + d₂, mul_nonneg hC₁ hC₂, fun m B hB hm => ?_⟩
    have e₁ := h₁ m B hB hm
    have e₂ := h₂ m B hB hm
    have hB0 : 0 ≤ B := zero_le_one.trans hB
    calc ‖R m * S m‖ = ‖R m‖ * ‖S m‖ := norm_mul _ _
      _ ≤ (C₁ * B ^ d₁) * (C₂ * B ^ d₂) := mul_le_mul e₁ e₂ (norm_nonneg _) (by positivity)
      _ = C₁ * C₂ * B ^ (d₁ + d₂) := by ring

end IsEntryPoly

private def detC (m : X₄ℂ) : ℂ := m 0 0 * m 1 1 - m 0 1 * m 1 0

private theorem detC_eq_det (m : X₄ℂ) : detC m = (Matrix.of m).det := IsEntryPoly.detCoords_eq m

private theorem isEntryPoly_detC : IsEntryPoly detC := IsEntryPoly.detCoords

private def frobC (m : X₄ℂ) : ℝ := ‖m 0 0‖ ^ 2 + ‖m 0 1‖ ^ 2 + ‖m 1 0‖ ^ 2 + ‖m 1 1‖ ^ 2

private theorem continuous_detC : Continuous detC := by
  unfold detC
  fun_prop

private theorem continuous_frobC : Continuous frobC := by
  unfold frobC
  fun_prop

private theorem frobC_nonneg (m : X₄ℂ) : 0 ≤ frobC m := by
  unfold frobC
  positivity

private theorem norm_detC_le (m : X₄ℂ) : ‖detC m‖ ≤ frobC m / 2 := by
  have h1 : ‖detC m‖ ≤ ‖m 0 0‖ * ‖m 1 1‖ + ‖m 0 1‖ * ‖m 1 0‖ := by
    calc ‖detC m‖ ≤ ‖m 0 0 * m 1 1‖ + ‖m 0 1 * m 1 0‖ := norm_sub_le _ _
      _ = ‖m 0 0‖ * ‖m 1 1‖ + ‖m 0 1‖ * ‖m 1 0‖ := by rw [norm_mul, norm_mul]
  unfold frobC
  nlinarith [h1, sq_nonneg (‖m 0 0‖ - ‖m 1 1‖), sq_nonneg (‖m 0 1‖ - ‖m 1 0‖)]

private theorem frobC_pos_of_detC_ne_zero {m : X₄ℂ} (hm : detC m ≠ 0) : 0 < frobC m := by
  have h1 : 0 < ‖detC m‖ := norm_pos_iff.mpr hm
  linarith [norm_detC_le m]

private theorem norm_sq_sub_mul_le (a b c d : ℂ) :
    ‖a * c - b * d‖ ^ 2 ≤ (‖a‖ ^ 2 + ‖b‖ ^ 2) * (‖c‖ ^ 2 + ‖d‖ ^ 2) := by
  have h1 : ‖a * c - b * d‖ ≤ ‖a‖ * ‖c‖ + ‖b‖ * ‖d‖ := by
    calc ‖a * c - b * d‖ ≤ ‖a * c‖ + ‖b * d‖ := norm_sub_le _ _
      _ = ‖a‖ * ‖c‖ + ‖b‖ * ‖d‖ := by rw [norm_mul, norm_mul]
  have h2 : (‖a‖ * ‖c‖ + ‖b‖ * ‖d‖) ^ 2 ≤ (‖a‖ ^ 2 + ‖b‖ ^ 2) * (‖c‖ ^ 2 + ‖d‖ ^ 2) := by
    nlinarith [sq_nonneg (‖a‖ * ‖d‖ - ‖b‖ * ‖c‖)]
  have h3 : ‖a * c - b * d‖ * ‖a * c - b * d‖ ≤ (‖a‖ * ‖c‖ + ‖b‖ * ‖d‖) * (‖a‖ * ‖c‖ + ‖b‖ * ‖d‖) :=
    mul_le_mul h1 h1 (norm_nonneg _) (by positivity)
  nlinarith [h2, h3]

private theorem norm_detC_sq_mul_le (m : X₄ℂ) (x Y : ℂ) :
    ‖detC m‖ ^ 2 * (‖x‖ ^ 2 + ‖Y‖ ^ 2) ≤ qForm m x Y * frobC m := by
  have eY : detC m * Y = (Y * m 0 0 + x * m 1 0) * m 1 1 - (Y * m 0 1 + x * m 1 1) * m 1 0 := by
    unfold detC
    ring
  have ex : detC m * x = (Y * m 0 1 + x * m 1 1) * m 0 0 - (Y * m 0 0 + x * m 1 0) * m 0 1 := by
    unfold detC
    ring
  have hY := norm_sq_sub_mul_le (Y * m 0 0 + x * m 1 0) (Y * m 0 1 + x * m 1 1) (m 1 1) (m 1 0)
  rw [← eY, norm_mul, mul_pow] at hY
  have hx := norm_sq_sub_mul_le (Y * m 0 1 + x * m 1 1) (Y * m 0 0 + x * m 1 0) (m 0 0) (m 0 1)
  rw [← ex, norm_mul, mul_pow] at hx
  unfold qForm frobC
  nlinarith [hY, hx]

private theorem eventually_qForm_ge {m₀ : X₄ℂ} (hm₀ : detC m₀ ≠ 0) :
    ∃ σ : ℝ, 0 < σ ∧ ∀ᶠ m in nhds m₀, ∀ x Y : ℂ, σ * (‖x‖ ^ 2 + ‖Y‖ ^ 2) ≤ qForm m x Y := by
  have hd : 0 < ‖detC m₀‖ ^ 2 := pow_pos (norm_pos_iff.mpr hm₀) 2
  have hf : 0 < frobC m₀ := frobC_pos_of_detC_ne_zero hm₀
  have hf' : frobC m₀ ≠ 0 := hf.ne'
  refine ⟨‖detC m₀‖ ^ 2 / (4 * frobC m₀), by positivity, ?_⟩
  have h1 : ∀ᶠ m in nhds m₀, ‖detC m₀‖ ^ 2 / 2 < ‖detC m‖ ^ 2 :=
    continuousAt_const.eventually_lt (continuous_detC.norm.pow 2).continuousAt
      (by linarith : ‖detC m₀‖ ^ 2 / 2 < ‖detC m₀‖ ^ 2)
  have h2 : ∀ᶠ m in nhds m₀, frobC m < 2 * frobC m₀ :=
    continuous_frobC.continuousAt.eventually_lt continuousAt_const (by linarith : frobC m₀ < 2 * frobC m₀)
  filter_upwards [h1, h2] with m hm1 hm2 x Y
  have hdm : detC m ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hm1
    nlinarith [hm1, hd]
  have hfm : 0 < frobC m := frobC_pos_of_detC_ne_zero hdm
  have hσ : ‖detC m₀‖ ^ 2 / (4 * frobC m₀) * frobC m ≤ ‖detC m‖ ^ 2 := by
    have hσ0 : 0 ≤ ‖detC m₀‖ ^ 2 / (4 * frobC m₀) := by positivity
    have h3 := mul_le_mul_of_nonneg_left hm2.le hσ0
    have e : ‖detC m₀‖ ^ 2 / (4 * frobC m₀) * (2 * frobC m₀) = ‖detC m₀‖ ^ 2 / 2 := by
      field_simp
      ring
    linarith
  have hs : 0 ≤ ‖x‖ ^ 2 + ‖Y‖ ^ 2 := by positivity
  have h3 : ‖detC m₀‖ ^ 2 / (4 * frobC m₀) * (‖x‖ ^ 2 + ‖Y‖ ^ 2) * frobC m ≤ qForm m x Y * frobC m :=
    calc ‖detC m₀‖ ^ 2 / (4 * frobC m₀) * (‖x‖ ^ 2 + ‖Y‖ ^ 2) * frobC m
        = (‖detC m₀‖ ^ 2 / (4 * frobC m₀) * frobC m) * (‖x‖ ^ 2 + ‖Y‖ ^ 2) := by ring
      _ ≤ ‖detC m‖ ^ 2 * (‖x‖ ^ 2 + ‖Y‖ ^ 2) := mul_le_mul_of_nonneg_right hσ hs
      _ ≤ qForm m x Y * frobC m := norm_detC_sq_mul_le m x Y
  exact le_of_mul_le_mul_right h3 hfm

private theorem ofReal_qForm_eq_of_rows {m : X₄ℂ} {c : ℂ} (h0 : m 0 0 * conj (m 0 0) + m 0 1 * conj (m 0 1) = c)
    (h1 : m 1 0 * conj (m 1 0) + m 1 1 * conj (m 1 1) = 1)
    (h01 : m 0 0 * conj (m 1 0) + m 0 1 * conj (m 1 1) = 0)
    (h10 : m 1 0 * conj (m 0 0) + m 1 1 * conj (m 0 1) = 0) (x Y : ℂ) :
    ((qForm m x Y : ℝ) : ℂ) = x * conj x + c * (Y * conj Y) := by
  have e : ((qForm m x Y : ℝ) : ℂ) =
      (Y * m 0 0 + x * m 1 0) * conj (Y * m 0 0 + x * m 1 0) +
        (Y * m 0 1 + x * m 1 1) * conj (Y * m 0 1 + x * m 1 1) := by
    simp only [qForm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  rw [e]
  simp only [map_add, map_mul]
  linear_combination (Y * conj Y) * h0 + (Y * conj x) * h01 + (x * conj Y) * h10 + (x * conj x) * h1

private theorem qForm_eq_of_rows {m : X₄ℂ} {ρ : ℝ}
    (h0 : m 0 0 * conj (m 0 0) + m 0 1 * conj (m 0 1) = ((ρ ^ 2 : ℝ) : ℂ))
    (h1 : m 1 0 * conj (m 1 0) + m 1 1 * conj (m 1 1) = 1)
    (h01 : m 0 0 * conj (m 1 0) + m 0 1 * conj (m 1 1) = 0)
    (h10 : m 1 0 * conj (m 0 0) + m 1 1 * conj (m 0 1) = 0) (x Y : ℂ) :
    qForm m x Y = ‖x‖ ^ 2 + ρ ^ 2 * ‖Y‖ ^ 2 := by
  have h := ofReal_qForm_eq_of_rows h0 h1 h01 h10 x Y
  simp only [Complex.mul_conj, Complex.normSq_eq_norm_sq] at h
  exact_mod_cast h

private theorem one_add_pow_le_exp (d : ℕ) {c : ℝ} (hc : 0 < c) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s : ℝ, 0 ≤ s → (1 + s) ^ d ≤ K * Real.exp (c * s) := by
  refine ⟨(d.factorial : ℝ) * Real.exp c / c ^ d, by positivity, fun s hs => ?_⟩
  have h : (c * (1 + s)) ^ d / (d.factorial : ℝ) ≤ Real.exp (c * (1 + s)) := by
    exact Real.pow_div_factorial_le_exp _ (by positivity) d
  rw [mul_pow, div_le_iff₀ (by positivity), mul_add, mul_one, Real.exp_add] at h
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  nlinarith [h]

private theorem one_add_norm_add_norm_le (x Y : ℂ) : 1 + ‖x‖ + ‖Y‖ ≤ 2 * (1 + (‖x‖ ^ 2 + ‖Y‖ ^ 2)) := by
  nlinarith [sq_nonneg (‖x‖ - 1 / 2), sq_nonneg (‖Y‖ - 1 / 2), norm_nonneg x, norm_nonneg Y]

private theorem entry_norm_le_norm (m : X₄ℂ) (i j : Fin 2) : ‖m i j‖ ≤ ‖m‖ :=
  (norm_le_pi_norm (m i) j).trans (norm_le_pi_norm m i)

private theorem exp_mul_exp_half (c s : ℝ) :
    Real.exp (c / 2 * s) * Real.exp (-c * s) = Real.exp (-(c / 2) * s) := by
  rw [← Real.exp_add]
  congr 1
  ring

private theorem one_add_add_le (a b : ℝ) : 1 + a + b ≤ 2 * (1 + (a ^ 2 + b ^ 2)) := by
  nlinarith [sq_nonneg (a - 1 / 4), sq_nonneg (b - 1 / 4)]

namespace IsPoly

private theorem phiFam_bound {Q : X₄ℂ → ℂ → ℂ → ℂ} (hQ : IsPoly Q) {R σ : ℝ} (hR : 0 ≤ R) (hσ : 0 < σ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ m : X₄ℂ, ‖m‖ ≤ R → (∀ x Y : ℂ, σ * (‖x‖ ^ 2 + ‖Y‖ ^ 2) ≤ qForm m x Y) →
      ∀ x Y : ℂ, ‖phiFam Q m x Y‖ ≤ K * Real.exp (-(2 * Real.pi * σ / 2) * (‖x‖ ^ 2 + ‖Y‖ ^ 2)) := by
  obtain ⟨C, d, hC, hsize⟩ := hQ.norm_le_of_gen_le
  obtain ⟨K₀, hK₀, habs⟩ := one_add_pow_le_exp d (c := 2 * Real.pi * σ / 2) (by positivity)
  refine ⟨C * (1 + R) ^ d * 2 ^ d * K₀, by positivity, fun m hm hq x Y => ?_⟩
  have hs : 0 ≤ ‖x‖ ^ 2 + ‖Y‖ ^ 2 := by positivity
  have hax := norm_nonneg x
  have haY := norm_nonneg Y
  have hB1 : (1 : ℝ) ≤ 1 + ‖x‖ + ‖Y‖ := by linarith
  have hR1 : (1 : ℝ) ≤ 1 + R := by linarith
  have hB1' : (0 : ℝ) ≤ 1 + ‖x‖ + ‖Y‖ := by linarith
  have hB : 1 ≤ (1 + R) * (1 + ‖x‖ + ‖Y‖) := one_le_mul_of_one_le_of_one_le hR1 hB1
  have hRB : 1 + R ≤ (1 + R) * (1 + ‖x‖ + ‖Y‖) := le_mul_of_one_le_right (by linarith) hB1
  have hBB : 1 + ‖x‖ + ‖Y‖ ≤ (1 + R) * (1 + ‖x‖ + ‖Y‖) := le_mul_of_one_le_left hB1' hR1
  have hent : ∀ i j, ‖m i j‖ ≤ R := fun i j => (entry_norm_le_norm m i j).trans hm
  have h1 : ∀ j, ‖m 1 j‖ ≤ (1 + R) * (1 + ‖x‖ + ‖Y‖) := fun j => by linarith [hent 1 j]
  have h0 : ∀ j, ‖Y * m 0 j‖ ≤ (1 + R) * (1 + ‖x‖ + ‖Y‖) := fun j => by
    rw [norm_mul]
    calc ‖Y‖ * ‖m 0 j‖ ≤ ‖Y‖ * R := mul_le_mul_of_nonneg_left (hent 0 j) haY
      _ ≤ (1 + ‖x‖ + ‖Y‖) * R := mul_le_mul_of_nonneg_right (by linarith) hR
      _ ≤ (1 + ‖x‖ + ‖Y‖) * (1 + R) := mul_le_mul_of_nonneg_left (by linarith) hB1'
      _ = (1 + R) * (1 + ‖x‖ + ‖Y‖) := mul_comm _ _
  have hx : ‖x‖ ≤ (1 + R) * (1 + ‖x‖ + ‖Y‖) := by linarith
  have hY : ‖Y‖ ≤ (1 + R) * (1 + ‖x‖ + ‖Y‖) := by linarith
  have hQb := hsize m x Y _ hB h1 h0 hx hY
  have h2 : (1 + ‖x‖ + ‖Y‖) ^ d ≤ 2 ^ d * (1 + (‖x‖ ^ 2 + ‖Y‖ ^ 2)) ^ d := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hB1' (one_add_add_le ‖x‖ ‖Y‖) d
  have h3 := habs (‖x‖ ^ 2 + ‖Y‖ ^ 2) hs
  have hpoly : ((1 + R) * (1 + ‖x‖ + ‖Y‖)) ^ d ≤
      (1 + R) ^ d * 2 ^ d * (K₀ * Real.exp (2 * Real.pi * σ / 2 * (‖x‖ ^ 2 + ‖Y‖ ^ 2))) := by
    rw [mul_pow]
    calc (1 + R) ^ d * (1 + ‖x‖ + ‖Y‖) ^ d ≤ (1 + R) ^ d * (2 ^ d * (1 + (‖x‖ ^ 2 + ‖Y‖ ^ 2)) ^ d) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ ≤ (1 + R) ^ d * (2 ^ d * (K₀ * Real.exp (2 * Real.pi * σ / 2 * (‖x‖ ^ 2 + ‖Y‖ ^ 2)))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 (by positivity)) (by positivity)
      _ = (1 + R) ^ d * 2 ^ d * (K₀ * Real.exp (2 * Real.pi * σ / 2 * (‖x‖ ^ 2 + ‖Y‖ ^ 2))) := by ring
  have hgauss : ‖gaussW m x Y‖ ≤ Real.exp (-(2 * Real.pi * σ) * (‖x‖ ^ 2 + ‖Y‖ ^ 2)) := by
    rw [norm_gaussW, Real.exp_le_exp]
    have := hq x Y
    nlinarith [Real.pi_pos]
  unfold phiFam
  rw [norm_mul]
  calc ‖Q m x Y‖ * ‖gaussW m x Y‖
      ≤ (C * ((1 + R) * (1 + ‖x‖ + ‖Y‖)) ^ d) * Real.exp (-(2 * Real.pi * σ) * (‖x‖ ^ 2 + ‖Y‖ ^ 2)) :=
        mul_le_mul hQb hgauss (norm_nonneg _) (by positivity)
    _ ≤ (C * ((1 + R) ^ d * 2 ^ d * (K₀ * Real.exp (2 * Real.pi * σ / 2 * (‖x‖ ^ 2 + ‖Y‖ ^ 2)))))
          * Real.exp (-(2 * Real.pi * σ) * (‖x‖ ^ 2 + ‖Y‖ ^ 2)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpoly hC) (Real.exp_pos _).le
    _ = C * (1 + R) ^ d * 2 ^ d * K₀ * Real.exp (-(2 * Real.pi * σ / 2) * (‖x‖ ^ 2 + ‖Y‖ ^ 2)) := by
        rw [← exp_mul_exp_half (2 * Real.pi * σ) (‖x‖ ^ 2 + ‖Y‖ ^ 2)]
        ring

private theorem phiFam_gate_bound {Q : X₄ℂ → ℂ → ℂ → ℂ} (hQ : IsPoly Q) :
    ∃ (K : ℝ) (d : ℕ), 0 ≤ K ∧ ∀ (m : X₄ℂ) (ρ : ℝ), (∀ j, ‖m 1 j‖ ≤ 1) → (∀ j, ‖m 0 j‖ ≤ ρ) →
      (∀ x t : ℂ, qForm m x t = ‖x‖ ^ 2 + ρ ^ 2 * ‖t‖ ^ 2) →
      ∀ x t : ℂ, ‖phiFam Q m x t‖ ≤
        K * (1 + ‖t‖) ^ d * Real.exp (-(2 * Real.pi / 2) * (‖x‖ ^ 2 + (ρ * ‖t‖) ^ 2)) := by
  obtain ⟨C, d, hC, hsize⟩ := hQ.norm_le_of_gen_le
  obtain ⟨K₀, hK₀, habs⟩ := one_add_pow_le_exp d (c := 2 * Real.pi / 2) (by positivity)
  refine ⟨C * 2 ^ d * K₀, d, by positivity, fun m ρ hbot htop hform x t => ?_⟩
  have hρ : 0 ≤ ρ := (norm_nonneg _).trans (htop 0)
  have hs : 0 ≤ ‖x‖ ^ 2 + (ρ * ‖t‖) ^ 2 := by positivity
  have hax := norm_nonneg x
  have hat := norm_nonneg t
  have haρt : 0 ≤ ρ * ‖t‖ := mul_nonneg hρ hat
  have hA1 : (1 : ℝ) ≤ 1 + ‖x‖ + ρ * ‖t‖ := by linarith
  have hA0 : (0 : ℝ) ≤ 1 + ‖x‖ + ρ * ‖t‖ := by linarith
  have hT1 : (1 : ℝ) ≤ 1 + ‖t‖ := by linarith
  have hB : 1 ≤ (1 + ‖x‖ + ρ * ‖t‖) * (1 + ‖t‖) := one_le_mul_of_one_le_of_one_le hA1 hT1
  have hAB : 1 + ‖x‖ + ρ * ‖t‖ ≤ (1 + ‖x‖ + ρ * ‖t‖) * (1 + ‖t‖) := le_mul_of_one_le_right hA0 hT1
  have hTB : 1 + ‖t‖ ≤ (1 + ‖x‖ + ρ * ‖t‖) * (1 + ‖t‖) := le_mul_of_one_le_left (by linarith) hA1
  have h1 : ∀ j, ‖m 1 j‖ ≤ (1 + ‖x‖ + ρ * ‖t‖) * (1 + ‖t‖) := fun j => by linarith [hbot j]
  have h0 : ∀ j, ‖t * m 0 j‖ ≤ (1 + ‖x‖ + ρ * ‖t‖) * (1 + ‖t‖) := fun j => by
    rw [norm_mul]
    have h' : ‖t‖ * ‖m 0 j‖ ≤ ‖t‖ * ρ := mul_le_mul_of_nonneg_left (htop j) hat
    have h'' : ‖t‖ * ρ = ρ * ‖t‖ := mul_comm _ _
    linarith
  have hx : ‖x‖ ≤ (1 + ‖x‖ + ρ * ‖t‖) * (1 + ‖t‖) := by linarith
  have ht : ‖t‖ ≤ (1 + ‖x‖ + ρ * ‖t‖) * (1 + ‖t‖) := by linarith
  have hQb := hsize m x t _ hB h1 h0 hx ht
  have h2 : (1 + ‖x‖ + ρ * ‖t‖) ^ d ≤ 2 ^ d * (1 + (‖x‖ ^ 2 + (ρ * ‖t‖) ^ 2)) ^ d := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hA0 (one_add_add_le ‖x‖ (ρ * ‖t‖)) d
  have h3 := habs (‖x‖ ^ 2 + (ρ * ‖t‖) ^ 2) hs
  have hpoly : ((1 + ‖x‖ + ρ * ‖t‖) * (1 + ‖t‖)) ^ d ≤
      2 ^ d * (K₀ * Real.exp (2 * Real.pi / 2 * (‖x‖ ^ 2 + (ρ * ‖t‖) ^ 2))) * (1 + ‖t‖) ^ d := by
    rw [mul_pow]
    calc (1 + ‖x‖ + ρ * ‖t‖) ^ d * (1 + ‖t‖) ^ d
        ≤ (2 ^ d * (1 + (‖x‖ ^ 2 + (ρ * ‖t‖) ^ 2)) ^ d) * (1 + ‖t‖) ^ d :=
          mul_le_mul_of_nonneg_right h2 (by positivity)
      _ ≤ (2 ^ d * (K₀ * Real.exp (2 * Real.pi / 2 * (‖x‖ ^ 2 + (ρ * ‖t‖) ^ 2)))) * (1 + ‖t‖) ^ d :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 (by positivity)) (by positivity)
  have hgauss : ‖gaussW m x t‖ = Real.exp (-(2 * Real.pi) * (‖x‖ ^ 2 + (ρ * ‖t‖) ^ 2)) := by
    rw [norm_gaussW, hform x t]
    congr 1
    ring
  unfold phiFam
  rw [norm_mul, hgauss]
  calc ‖Q m x t‖ * Real.exp (-(2 * Real.pi) * (‖x‖ ^ 2 + (ρ * ‖t‖) ^ 2))
      ≤ (C * ((1 + ‖x‖ + ρ * ‖t‖) * (1 + ‖t‖)) ^ d) * Real.exp (-(2 * Real.pi) * (‖x‖ ^ 2 + (ρ * ‖t‖) ^ 2)) :=
        mul_le_mul_of_nonneg_right hQb (Real.exp_pos _).le
    _ ≤ (C * (2 ^ d * (K₀ * Real.exp (2 * Real.pi / 2 * (‖x‖ ^ 2 + (ρ * ‖t‖) ^ 2))) * (1 + ‖t‖) ^ d))
          * Real.exp (-(2 * Real.pi) * (‖x‖ ^ 2 + (ρ * ‖t‖) ^ 2)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpoly hC) (Real.exp_pos _).le
    _ = C * 2 ^ d * K₀ * (1 + ‖t‖) ^ d * Real.exp (-(2 * Real.pi / 2) * (‖x‖ ^ 2 + (ρ * ‖t‖) ^ 2)) := by
        rw [← exp_mul_exp_half (2 * Real.pi) (‖x‖ ^ 2 + (ρ * ‖t‖) ^ 2)]
        ring

end IsPoly

open MeasureTheory in

private theorem integrable_exp_neg_mul_norm_sq {c : ℝ} (hc : 0 < c) :
    Integrable fun v : ℂ => Real.exp (-c * ‖v‖ ^ 2) := by
  have hb : (0 : ℝ) < ((c : ℂ)).re := by simpa using hc
  have hg := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add hb (0 : ℂ) (0 : ℂ)).norm
  refine hg.congr (Filter.Eventually.of_forall fun v => ?_)
  simp [Complex.norm_exp, pow_two]

namespace IsPoly

open MeasureTheory in

private theorem integrable_phiFam {Q : X₄ℂ → ℂ → ℂ → ℂ} (hQ : IsPoly Q) {m : X₄ℂ} (hm : detC m ≠ 0) (Y : ℂ) :
    Integrable fun x : ℂ => phiFam Q m x Y := by
  obtain ⟨σ, hσ, hev⟩ := eventually_qForm_ge hm
  have hq : ∀ x Y : ℂ, σ * (‖x‖ ^ 2 + ‖Y‖ ^ 2) ≤ qForm m x Y := hev.self_of_nhds
  obtain ⟨K, hK, hbound⟩ := hQ.phiFam_bound (R := ‖m‖) (norm_nonneg m) hσ
  have hc : 0 < 2 * Real.pi * σ / 2 := by positivity
  refine Integrable.mono' ((integrable_exp_neg_mul_norm_sq hc).const_mul
    (K * Real.exp (-(2 * Real.pi * σ / 2) * ‖Y‖ ^ 2))) ?_ ?_
  · exact (hQ.contDiff_x_phiFam m Y).continuous.aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun x => ?_
    calc ‖phiFam Q m x Y‖ ≤ K * Real.exp (-(2 * Real.pi * σ / 2) * (‖x‖ ^ 2 + ‖Y‖ ^ 2)) := hbound m le_rfl hq x Y
      _ = K * Real.exp (-(2 * Real.pi * σ / 2) * ‖Y‖ ^ 2) * Real.exp (-(2 * Real.pi * σ / 2) * ‖x‖ ^ 2) := by
          rw [mul_assoc K, ← Real.exp_add]
          congr 2
          ring

end IsPoly

private def wirtL₁ : ℂ →L[ℝ] (ℂ →L[ℝ] ℂ) := (ContinuousLinearMap.id ℝ ℂ).smulRight (ContinuousLinearMap.id ℝ ℂ)

private def wirtL₂ : ℂ →L[ℝ] (ℂ →L[ℝ] ℂ) := (ContinuousLinearMap.id ℝ ℂ).smulRight (Complex.conjCLE : ℂ →L[ℝ] ℂ)

private theorem norm_iteratedFDeriv_wirt_le {g₁ g₂ : ℂ → ℂ} (h₁ : ContDiff ℝ (⊤ : ℕ∞) g₁) (h₂ : ContDiff ℝ (⊤ : ℕ∞) g₂)
    (n : ℕ) (x : ℂ) :
    ‖iteratedFDeriv ℝ n (fun y => wirt (g₁ y) (g₂ y)) x‖ ≤
      ‖wirtL₁‖ * ‖iteratedFDeriv ℝ n g₁ x‖ + ‖wirtL₂‖ * ‖iteratedFDeriv ℝ n g₂ x‖ := by
  have h₁n : ContDiffAt ℝ n g₁ x := (contDiff_infty.1 h₁ n).contDiffAt
  have h₂n : ContDiffAt ℝ n g₂ x := (contDiff_infty.1 h₂ n).contDiffAt
  have hA : ContDiffAt ℝ n (fun y => g₁ y • (ContinuousLinearMap.id ℝ ℂ)) x := h₁n.smul_const _
  have hB : ContDiffAt ℝ n (fun y => g₂ y • (Complex.conjCLE : ℂ →L[ℝ] ℂ)) x := h₂n.smul_const _
  have e : (fun y => wirt (g₁ y) (g₂ y)) =
      (fun y => g₁ y • (ContinuousLinearMap.id ℝ ℂ)) + fun y => g₂ y • (Complex.conjCLE : ℂ →L[ℝ] ℂ) := by
    funext y
    simp only [wirt, Pi.add_apply]
  rw [e, iteratedFDeriv_add_apply hA hB, iteratedFDeriv_smul_const_apply h₁n, iteratedFDeriv_smul_const_apply h₂n]
  unfold wirtL₁ wirtL₂
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · exact ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _
  · exact ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _

private theorem phiFam_list_sum_nonneg (Qs : List (X₄ℂ → ℂ → ℂ → ℂ)) (m : X₄ℂ) (x t : ℂ) :
    0 ≤ (Qs.map fun Q' => ‖phiFam Q' m x t‖).sum := by
  induction Qs with
  | nil => simp
  | cons Q' Qs ih =>
    simp only [List.map_cons, List.sum_cons]
    exact add_nonneg (norm_nonneg _) ih

open MeasureTheory in
private theorem integrable_phiFam_list_sum (Qs : List (X₄ℂ → ℂ → ℂ → ℂ)) (hQs : ∀ Q' ∈ Qs, IsPoly Q') {m : X₄ℂ}
    (hm : detC m ≠ 0) (t : ℂ) : Integrable fun x : ℂ => (Qs.map fun Q' => ‖phiFam Q' m x t‖).sum := by
  induction Qs with
  | nil =>
    simp only [List.map_nil, List.sum_nil]
    exact integrable_zero _ _ _
  | cons Q' Qs ih =>
    simp only [List.map_cons, List.sum_cons]
    have h1 : IsPoly Q' := hQs Q' (by simp)
    exact (h1.integrable_phiFam hm t).norm.add (ih fun Q'' h => hQs Q'' (by simp [h]))

namespace IsPoly

private theorem norm_iteratedFDeriv_x_phiFam_le {Q : X₄ℂ → ℂ → ℂ → ℂ} (hQ : IsPoly Q) (n : ℕ) :
    ∃ (C : ℝ) (Qs : List (X₄ℂ → ℂ → ℂ → ℂ)), 0 ≤ C ∧ (∀ Q' ∈ Qs, IsPoly Q') ∧
      ∀ (m : X₄ℂ) (t x : ℂ), ‖iteratedFDeriv ℝ n (fun x => phiFam Q m x t) x‖ ≤
        C * (Qs.map fun Q' => ‖phiFam Q' m x t‖).sum := by
  induction n generalizing Q with
  | zero =>
    refine ⟨1, [Q], zero_le_one, ?_, fun m t x => ?_⟩
    · intro Q' hQ'
      rw [List.mem_singleton] at hQ'
      rw [hQ']
      exact hQ
    · simp [norm_iteratedFDeriv_zero]
  | succ n ih =>
    obtain ⟨Q₁, Q₂, hQ₁, hQ₂, hd⟩ := hQ.hasFDerivAt_x_phiFam
    obtain ⟨C₁, L₁, hC₁, hL₁, hb₁⟩ := ih hQ₁
    obtain ⟨C₂, L₂, hC₂, hL₂, hb₂⟩ := ih hQ₂
    refine ⟨‖wirtL₁‖ * C₁ + ‖wirtL₂‖ * C₂, L₁ ++ L₂,
      add_nonneg (mul_nonneg (ContinuousLinearMap.opNorm_nonneg wirtL₁) hC₁)
        (mul_nonneg (ContinuousLinearMap.opNorm_nonneg wirtL₂) hC₂), ?_, fun m t x => ?_⟩
    · intro Q' hQ'
      rcases List.mem_append.1 hQ' with h | h
      · exact hL₁ Q' h
      · exact hL₂ Q' h
    · have hfd : fderiv ℝ (fun x => phiFam Q m x t) = fun y => wirt (phiFam Q₁ m y t) (phiFam Q₂ m y t) :=
        funext fun y => (hd m y t).fderiv
      rw [← norm_iteratedFDeriv_fderiv, hfd]
      have h1 := norm_iteratedFDeriv_wirt_le (hQ₁.contDiff_x_phiFam m t) (hQ₂.contDiff_x_phiFam m t) n x
      have e₁ := hb₁ m t x
      have e₂ := hb₂ m t x
      have hS₁ := phiFam_list_sum_nonneg L₁ m x t
      have hS₂ := phiFam_list_sum_nonneg L₂ m x t
      have hw₁ := ContinuousLinearMap.opNorm_nonneg wirtL₁
      have hw₂ := ContinuousLinearMap.opNorm_nonneg wirtL₂
      have f₁ := mul_le_mul_of_nonneg_left e₁ hw₁
      have f₂ := mul_le_mul_of_nonneg_left e₂ hw₂
      rw [List.map_append, List.sum_append]
      refine h1.trans ?_
      nlinarith [f₁, f₂, mul_nonneg (mul_nonneg hw₁ hC₁) hS₂, mul_nonneg (mul_nonneg hw₂ hC₂) hS₁]

open MeasureTheory in

private theorem
    integrable_norm_iteratedFDeriv_x_phiFam {Q : X₄ℂ → ℂ → ℂ → ℂ} (hQ : IsPoly Q) {m : X₄ℂ} (hm : detC m ≠ 0)
    (t : ℂ) (n : ℕ) : Integrable fun x : ℂ => ‖iteratedFDeriv ℝ n (fun x => phiFam Q m x t) x‖ := by
  obtain ⟨C, Qs, _, hQs, hb⟩ := hQ.norm_iteratedFDeriv_x_phiFam_le n
  refine ((integrable_phiFam_list_sum Qs hQs hm t).const_mul C).mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
  · exact (contDiff_infty.1 (hQ.contDiff_x_phiFam m t) n).continuous_iteratedFDeriv'.norm.aestronglyMeasurable
  · simp only [norm_norm]
    exact hb m t x

open MeasureTheory in
open scoped FourierTransform in

private theorem fourier_slice_bound {Q : X₄ℂ → ℂ → ℂ → ℂ} (hQ : IsPoly Q) {m : X₄ℂ} (hm : detC m ≠ 0) (t : ℂ) (n : ℕ)
    (w : ℂ) :
    ‖w‖ ^ n * ‖𝓕 (fun x : ℂ => phiFam Q m x t) w‖ ≤
      2 ^ n * ∑ j ∈ Finset.range (n + 1), ∫ x : ℂ, ‖iteratedFDeriv ℝ j (fun x : ℂ => phiFam Q m x t) x‖ := by
  have hint : ∀ (k j : ℕ), (k : ℕ∞) ≤ (0 : ℕ∞) → (j : ℕ∞) ≤ (⊤ : ℕ∞) →
      Integrable fun v : ℂ => ‖v‖ ^ k * ‖iteratedFDeriv ℝ j (fun x : ℂ => phiFam Q m x t) v‖ := by
    intro k j hk _
    have hk0 : k = 0 := by simpa using hk
    subst hk0
    simp only [pow_zero, one_mul]
    exact hQ.integrable_norm_iteratedFDeriv_x_phiFam hm t j
  have key := Real.pow_mul_norm_iteratedFDeriv_fourier_le (K := 0) (N := ⊤) (hQ.contDiff_x_phiFam m t) hint
    (k := 0) (n := n) (by simp) le_top w
  rw [norm_iteratedFDeriv_zero] at key
  refine key.trans (le_of_eq ?_)
  rw [Finset.sum_product]
  simp

end IsPoly

open MeasureTheory in

private def gaussInt (c : ℝ) : ℝ := ∫ x : ℂ, Real.exp (-c * ‖x‖ ^ 2)

open MeasureTheory in
private theorem gaussInt_nonneg (c : ℝ) : 0 ≤ gaussInt c := integral_nonneg fun _ => (Real.exp_pos _).le

private theorem dom_add {a b K₁ K₂ s E : ℝ} {d₁ d₂ : ℕ} (hs : 0 ≤ s) (hE : 0 ≤ E) (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (h₁ : a ≤ K₁ * (1 + s) ^ d₁ * E) (h₂ : b ≤ K₂ * (1 + s) ^ d₂ * E) :
    a + b ≤ (K₁ + K₂) * (1 + s) ^ max d₁ d₂ * E := by
  have h1s : (1 : ℝ) ≤ 1 + s := by linarith
  have p₁ : (1 + s) ^ d₁ ≤ (1 + s) ^ max d₁ d₂ := pow_le_pow_right₀ h1s (le_max_left _ _)
  have p₂ : (1 + s) ^ d₂ ≤ (1 + s) ^ max d₁ d₂ := pow_le_pow_right₀ h1s (le_max_right _ _)
  have q₁ : K₁ * (1 + s) ^ d₁ * E ≤ K₁ * (1 + s) ^ max d₁ d₂ * E :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left p₁ hK₁) hE
  have q₂ : K₂ * (1 + s) ^ d₂ * E ≤ K₂ * (1 + s) ^ max d₁ d₂ * E :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left p₂ hK₂) hE
  calc a + b ≤ K₁ * (1 + s) ^ max d₁ d₂ * E + K₂ * (1 + s) ^ max d₁ d₂ * E := add_le_add (h₁.trans q₁) (h₂.trans q₂)
    _ = (K₁ + K₂) * (1 + s) ^ max d₁ d₂ * E := by ring

private theorem
    list_ball_bound (L : List (X₄ℂ → ℂ → ℂ → ℂ)) (hL : ∀ Q' ∈ L, IsPoly Q') {R σ : ℝ} (hR : 0 ≤ R) (hσ : 0 < σ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ m : X₄ℂ, ‖m‖ ≤ R → (∀ x Y : ℂ, σ * (‖x‖ ^ 2 + ‖Y‖ ^ 2) ≤ qForm m x Y) → ∀ x t : ℂ,
      (L.map fun Q' => ‖phiFam Q' m x t‖).sum ≤ K * Real.exp (-(2 * Real.pi * σ / 2) * (‖x‖ ^ 2 + ‖t‖ ^ 2)) := by
  induction L with
  | nil => exact ⟨0, le_rfl, fun m _ _ x t => by simp⟩
  | cons Q' L ih =>
    obtain ⟨K₁, hK₁, h₁⟩ := (hL Q' (by simp)).phiFam_bound hR hσ
    obtain ⟨K₂, hK₂, h₂⟩ := ih fun Q'' h => hL Q'' (by simp [h])
    refine ⟨K₁ + K₂, add_nonneg hK₁ hK₂, fun m hm hq x t => ?_⟩
    simp only [List.map_cons, List.sum_cons]
    have e₁ := h₁ m hm hq x t
    have e₂ := h₂ m hm hq x t
    nlinarith [e₁, e₂]

private theorem list_gate_bound (L : List (X₄ℂ → ℂ → ℂ → ℂ)) (hL : ∀ Q' ∈ L, IsPoly Q') :
    ∃ (K : ℝ) (d : ℕ), 0 ≤ K ∧ ∀ (m : X₄ℂ) (ρ : ℝ), (∀ j, ‖m 1 j‖ ≤ 1) → (∀ j, ‖m 0 j‖ ≤ ρ) →
      (∀ x t : ℂ, qForm m x t = ‖x‖ ^ 2 + ρ ^ 2 * ‖t‖ ^ 2) → ∀ x t : ℂ,
      (L.map fun Q' => ‖phiFam Q' m x t‖).sum ≤
        K * (1 + ‖t‖) ^ d * Real.exp (-(2 * Real.pi / 2) * (‖x‖ ^ 2 + (ρ * ‖t‖) ^ 2)) := by
  induction L with
  | nil => exact ⟨0, 0, le_rfl, fun m ρ _ _ _ x t => by simp⟩
  | cons Q' L ih =>
    obtain ⟨K₁, d₁, hK₁, h₁⟩ := (hL Q' (by simp)).phiFam_gate_bound
    obtain ⟨K₂, d₂, hK₂, h₂⟩ := ih fun Q'' h => hL Q'' (by simp [h])
    refine ⟨K₁ + K₂, max d₁ d₂, add_nonneg hK₁ hK₂, fun m ρ hbot htop hform x t => ?_⟩
    simp only [List.map_cons, List.sum_cons]
    exact dom_add (norm_nonneg t) (Real.exp_pos _).le hK₁ hK₂ (h₁ m ρ hbot htop hform x t)
      (h₂ m ρ hbot htop hform x t)

namespace IsPoly

open MeasureTheory in

private theorem integral_iteratedFDeriv_ball_bound {Q : X₄ℂ → ℂ → ℂ → ℂ} (hQ : IsPoly Q) (j : ℕ) {R σ : ℝ} (hR : 0 ≤ R)
    (hσ : 0 < σ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ m : X₄ℂ, ‖m‖ ≤ R → (∀ x Y : ℂ, σ * (‖x‖ ^ 2 + ‖Y‖ ^ 2) ≤ qForm m x Y) → ∀ t : ℂ,
      (∫ x : ℂ, ‖iteratedFDeriv ℝ j (fun x => phiFam Q m x t) x‖) ≤
        K * Real.exp (-(2 * Real.pi * σ / 2) * ‖t‖ ^ 2) := by
  obtain ⟨C, L, hC, hL, hb⟩ := hQ.norm_iteratedFDeriv_x_phiFam_le j
  obtain ⟨K, hK, hdom⟩ := list_ball_bound L hL hR hσ
  refine ⟨C * K * gaussInt (2 * Real.pi * σ / 2), mul_nonneg (mul_nonneg hC hK) (gaussInt_nonneg _),
    fun m hm hq t => ?_⟩
  have hc : 0 < 2 * Real.pi * σ / 2 := by positivity
  have hint : Integrable fun x : ℂ =>
      C * K * Real.exp (-(2 * Real.pi * σ / 2) * ‖t‖ ^ 2) * Real.exp (-(2 * Real.pi * σ / 2) * ‖x‖ ^ 2) :=
    (integrable_exp_neg_mul_norm_sq hc).const_mul _
  calc (∫ x : ℂ, ‖iteratedFDeriv ℝ j (fun x => phiFam Q m x t) x‖)
      ≤ ∫ x : ℂ, C * K * Real.exp (-(2 * Real.pi * σ / 2) * ‖t‖ ^ 2) *
          Real.exp (-(2 * Real.pi * σ / 2) * ‖x‖ ^ 2) := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => norm_nonneg _) hint
          (Filter.Eventually.of_forall fun x => ?_)
        have h1 := hb m t x
        have h2 := hdom m hm hq x t
        have h3 : Real.exp (-(2 * Real.pi * σ / 2) * (‖x‖ ^ 2 + ‖t‖ ^ 2)) =
            Real.exp (-(2 * Real.pi * σ / 2) * ‖t‖ ^ 2) * Real.exp (-(2 * Real.pi * σ / 2) * ‖x‖ ^ 2) := by
          rw [← Real.exp_add]
          congr 1
          ring
        calc ‖iteratedFDeriv ℝ j (fun x => phiFam Q m x t) x‖ ≤ C * (L.map fun Q' => ‖phiFam Q' m x t‖).sum := h1
          _ ≤ C * (K * Real.exp (-(2 * Real.pi * σ / 2) * (‖x‖ ^ 2 + ‖t‖ ^ 2))) := mul_le_mul_of_nonneg_left h2 hC
          _ = C * K * Real.exp (-(2 * Real.pi * σ / 2) * ‖t‖ ^ 2) * Real.exp (-(2 * Real.pi * σ / 2) * ‖x‖ ^ 2) := by
              rw [h3]
              ring
    _ = C * K * gaussInt (2 * Real.pi * σ / 2) * Real.exp (-(2 * Real.pi * σ / 2) * ‖t‖ ^ 2) := by
        rw [integral_const_mul]
        unfold gaussInt
        ring

open MeasureTheory in

private theorem integral_iteratedFDeriv_gate_bound {Q : X₄ℂ → ℂ → ℂ → ℂ} (hQ : IsPoly Q) (j : ℕ) :
    ∃ (K : ℝ) (d : ℕ), 0 ≤ K ∧ ∀ (m : X₄ℂ) (ρ : ℝ), (∀ i, ‖m 1 i‖ ≤ 1) → (∀ i, ‖m 0 i‖ ≤ ρ) →
      (∀ x t : ℂ, qForm m x t = ‖x‖ ^ 2 + ρ ^ 2 * ‖t‖ ^ 2) → ∀ t : ℂ,
      (∫ x : ℂ, ‖iteratedFDeriv ℝ j (fun x => phiFam Q m x t) x‖) ≤
        K * (1 + ‖t‖) ^ d * Real.exp (-(2 * Real.pi / 2) * (ρ * ‖t‖) ^ 2) := by
  obtain ⟨C, L, hC, hL, hb⟩ := hQ.norm_iteratedFDeriv_x_phiFam_le j
  obtain ⟨K, d, hK, hdom⟩ := list_gate_bound L hL
  refine ⟨C * K * gaussInt (2 * Real.pi / 2), d, mul_nonneg (mul_nonneg hC hK) (gaussInt_nonneg _),
    fun m ρ hbot htop hform t => ?_⟩
  have hc : 0 < 2 * Real.pi / 2 := by positivity
  have hint : Integrable fun x : ℂ =>
      C * K * (1 + ‖t‖) ^ d * Real.exp (-(2 * Real.pi / 2) * (ρ * ‖t‖) ^ 2) *
        Real.exp (-(2 * Real.pi / 2) * ‖x‖ ^ 2) :=
    (integrable_exp_neg_mul_norm_sq hc).const_mul _
  calc (∫ x : ℂ, ‖iteratedFDeriv ℝ j (fun x => phiFam Q m x t) x‖)
      ≤ ∫ x : ℂ, C * K * (1 + ‖t‖) ^ d * Real.exp (-(2 * Real.pi / 2) * (ρ * ‖t‖) ^ 2) *
          Real.exp (-(2 * Real.pi / 2) * ‖x‖ ^ 2) := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => norm_nonneg _) hint
          (Filter.Eventually.of_forall fun x => ?_)
        have h1 := hb m t x
        have h2 := hdom m ρ hbot htop hform x t
        have h3 : Real.exp (-(2 * Real.pi / 2) * (‖x‖ ^ 2 + (ρ * ‖t‖) ^ 2)) =
            Real.exp (-(2 * Real.pi / 2) * (ρ * ‖t‖) ^ 2) * Real.exp (-(2 * Real.pi / 2) * ‖x‖ ^ 2) := by
          rw [← Real.exp_add]
          congr 1
          ring
        calc ‖iteratedFDeriv ℝ j (fun x => phiFam Q m x t) x‖ ≤ C * (L.map fun Q' => ‖phiFam Q' m x t‖).sum := h1
          _ ≤ C * (K * (1 + ‖t‖) ^ d * Real.exp (-(2 * Real.pi / 2) * (‖x‖ ^ 2 + (ρ * ‖t‖) ^ 2))) :=
              mul_le_mul_of_nonneg_left h2 hC
          _ = C * K * (1 + ‖t‖) ^ d * Real.exp (-(2 * Real.pi / 2) * (ρ * ‖t‖) ^ 2) *
                Real.exp (-(2 * Real.pi / 2) * ‖x‖ ^ 2) := by
              rw [h3]
              ring
    _ = C * K * gaussInt (2 * Real.pi / 2) * (1 + ‖t‖) ^ d * Real.exp (-(2 * Real.pi / 2) * (ρ * ‖t‖) ^ 2) := by
        rw [integral_const_mul]
        unfold gaussInt
        ring

open MeasureTheory in

private theorem
    sum_integral_iteratedFDeriv_ball_bound {Q : X₄ℂ → ℂ → ℂ → ℂ} (hQ : IsPoly Q) (n : ℕ) {R σ : ℝ} (hR : 0 ≤ R)
    (hσ : 0 < σ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ m : X₄ℂ, ‖m‖ ≤ R → (∀ x Y : ℂ, σ * (‖x‖ ^ 2 + ‖Y‖ ^ 2) ≤ qForm m x Y) → ∀ t : ℂ,
      (∑ j ∈ Finset.range (n + 1), ∫ x : ℂ, ‖iteratedFDeriv ℝ j (fun x => phiFam Q m x t) x‖) ≤
        K * Real.exp (-(2 * Real.pi * σ / 2) * ‖t‖ ^ 2) := by
  induction n with
  | zero =>
    obtain ⟨K, hK, h⟩ := hQ.integral_iteratedFDeriv_ball_bound 0 hR hσ
    refine ⟨K, hK, fun m hm hq t => ?_⟩
    simp only [zero_add, Finset.sum_range_one]
    exact h m hm hq t
  | succ n ih =>
    obtain ⟨K₁, hK₁, h₁⟩ := ih
    obtain ⟨K₂, hK₂, h₂⟩ := hQ.integral_iteratedFDeriv_ball_bound (n + 1) hR hσ
    refine ⟨K₁ + K₂, add_nonneg hK₁ hK₂, fun m hm hq t => ?_⟩
    rw [Finset.sum_range_succ]
    have e₁ := h₁ m hm hq t
    have e₂ := h₂ m hm hq t
    nlinarith [e₁, e₂]

open MeasureTheory in

private theorem sum_integral_iteratedFDeriv_gate_bound {Q : X₄ℂ → ℂ → ℂ → ℂ} (hQ : IsPoly Q) (n : ℕ) :
    ∃ (K : ℝ) (d : ℕ), 0 ≤ K ∧ ∀ (m : X₄ℂ) (ρ : ℝ), (∀ i, ‖m 1 i‖ ≤ 1) → (∀ i, ‖m 0 i‖ ≤ ρ) →
      (∀ x t : ℂ, qForm m x t = ‖x‖ ^ 2 + ρ ^ 2 * ‖t‖ ^ 2) → ∀ t : ℂ,
      (∑ j ∈ Finset.range (n + 1), ∫ x : ℂ, ‖iteratedFDeriv ℝ j (fun x => phiFam Q m x t) x‖) ≤
        K * (1 + ‖t‖) ^ d * Real.exp (-(2 * Real.pi / 2) * (ρ * ‖t‖) ^ 2) := by
  induction n with
  | zero =>
    obtain ⟨K, d, hK, h⟩ := hQ.integral_iteratedFDeriv_gate_bound 0
    refine ⟨K, d, hK, fun m ρ hbot htop hform t => ?_⟩
    simp only [zero_add, Finset.sum_range_one]
    exact h m ρ hbot htop hform t
  | succ n ih =>
    obtain ⟨K₁, d₁, hK₁, h₁⟩ := ih
    obtain ⟨K₂, d₂, hK₂, h₂⟩ := hQ.integral_iteratedFDeriv_gate_bound (n + 1)
    refine ⟨K₁ + K₂, max d₁ d₂, add_nonneg hK₁ hK₂, fun m ρ hbot htop hform t => ?_⟩
    rw [Finset.sum_range_succ]
    exact dom_add (norm_nonneg t) (Real.exp_pos _).le hK₁ hK₂ (h₁ m ρ hbot htop hform t) (h₂ m ρ hbot htop hform t)

end IsPoly

namespace IsPoly

private theorem
    continuous_xY {P : X₄ℂ → ℂ → ℂ → ℂ} (h : IsPoly P) (m : X₄ℂ) : Continuous fun p : ℂ × ℂ => P m p.1 p.2 := by
  have hc : Continuous fun z : ℂ => conj z := Complex.continuous_conj
  induction h with
  | const c => exact continuous_const
  | rowOne j => exact continuous_const
  | rowOneBar j => exact continuous_const
  | rowZeroY j => exact continuous_snd.mul continuous_const
  | rowZeroYBar j => exact (hc.comp continuous_snd).mul continuous_const
  | varX => exact continuous_fst
  | varXBar => exact hc.comp continuous_fst
  | varY => exact continuous_snd
  | varYBar => exact hc.comp continuous_snd
  | add _ _ ihP ihQ => exact ihP.add ihQ
  | mul _ _ ihP ihQ => exact ihP.mul ihQ

end IsPoly

private theorem continuous_gaussW_xY (m : X₄ℂ) : Continuous fun p : ℂ × ℂ => gaussW m p.1 p.2 :=
  Complex.continuous_exp.comp (isPoly_expo.continuous_xY m)

namespace IsPoly

private theorem continuous_phiFam_xY {P : X₄ℂ → ℂ → ℂ → ℂ} (h : IsPoly P) (m : X₄ℂ) :
    Continuous fun p : ℂ × ℂ => phiFam P m p.1 p.2 :=
  (h.continuous_xY m).mul (continuous_gaussW_xY m)

end IsPoly

private structure Freq where

  fr : ℂ → ℂ

  c : ℝ
  c_pos : 0 < c
  norm_fr : ∀ t : ℂ, t ≠ 0 → ‖fr t‖ = c * ‖t‖⁻¹
  measurable_fr : Measurable fr

  jac : ℝ

open scoped FourierTransform in

private def innFC (F : Freq) (P : X₄ℂ → ℂ → ℂ → ℂ) (m : X₄ℂ) (t : ℂ) : ℂ :=
  ((F.jac * ‖t‖⁻¹ ^ 2 : ℝ) : ℂ) * 𝓕 (fun x : ℂ => phiFam P m x t) (F.fr t)

private structure IsGateC (ρ : ℝ) (m : X₄ℂ) : Prop where
  bot : ∀ i, ‖m 1 i‖ ≤ 1
  top : ∀ i, ‖m 0 i‖ ≤ ρ
  form : ∀ x t : ℂ, qForm m x t = ‖x‖ ^ 2 + ρ ^ 2 * ‖t‖ ^ 2
  detC_ne : detC m ≠ 0

namespace IsPoly

open MeasureTheory in
private theorem
    measurable_innFC (F : Freq) {Q : X₄ℂ → ℂ → ℂ → ℂ} (hQ : IsPoly Q) (m : X₄ℂ) : Measurable (innFC F Q m) := by
  have hi : Measurable fun p : ℂ × ℂ => inner ℝ p.2 (F.fr p.1) :=
    measurable_snd.inner (F.measurable_fr.comp measurable_fst)
  have hk : Measurable fun p : ℂ × ℂ =>
      Complex.exp (((-2 * Real.pi * inner ℝ p.2 (F.fr p.1) : ℝ) : ℂ) * Complex.I) :=
    Complex.measurable_exp.comp ((Complex.measurable_ofReal.comp (hi.const_mul (-2 * Real.pi))).mul_const Complex.I)
  have h2 : Measurable fun p : ℂ × ℂ => phiFam Q m p.2 p.1 :=
    ((hQ.continuous_phiFam_xY m).comp continuous_swap).measurable
  have hjoint : StronglyMeasurable fun p : ℂ × ℂ =>
      Complex.exp (((-2 * Real.pi * inner ℝ p.2 (F.fr p.1) : ℝ) : ℂ) * Complex.I) * phiFam Q m p.2 p.1 :=
    (hk.mul h2).stronglyMeasurable
  have hG : Measurable fun t : ℂ =>
      ∫ x : ℂ, Complex.exp (((-2 * Real.pi * inner ℝ x (F.fr t) : ℝ) : ℂ) * Complex.I) * phiFam Q m x t :=
    hjoint.integral_prod_right'.measurable
  have e : innFC F Q m = fun t => ((F.jac * ‖t‖⁻¹ ^ 2 : ℝ) : ℂ) *
      ∫ x : ℂ, Complex.exp (((-2 * Real.pi * inner ℝ x (F.fr t) : ℝ) : ℂ) * Complex.I) * phiFam Q m x t := by
    funext t
    rw [innFC, Real.fourier_eq']
    simp only [smul_eq_mul]
  rw [e]
  exact (Complex.measurable_ofReal.comp ((measurable_norm.inv.pow_const 2).const_mul F.jac)).mul hG

private theorem norm_innFC_prefactor (F : Freq) (t : ℂ) : ‖((F.jac * ‖t‖⁻¹ ^ 2 : ℝ) : ℂ)‖ = |F.jac| * ‖t‖⁻¹ ^ 2 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖t‖⁻¹ ^ 2)]

private theorem unit_pow (F : Freq) {t : ℂ} (ht : t ≠ 0) (n : ℕ) : (F.c⁻¹ * ‖t‖) ^ n * ‖F.fr t‖ ^ n = 1 := by
  rw [F.norm_fr t ht, ← mul_pow]
  have h3 : ‖t‖ * ‖t‖⁻¹ = 1 := mul_inv_cancel₀ (norm_ne_zero_iff.mpr ht)
  have h4 : F.c⁻¹ * F.c = 1 := inv_mul_cancel₀ F.c_pos.ne'
  rw [show F.c⁻¹ * ‖t‖ * (F.c * ‖t‖⁻¹) = F.c⁻¹ * F.c * (‖t‖ * ‖t‖⁻¹) by ring, h3, h4, one_mul, one_pow]

open scoped FourierTransform in

private theorem
    norm_fourier_slice_le (F : Freq) {Q : X₄ℂ → ℂ → ℂ → ℂ} (hQ : IsPoly Q) {m : X₄ℂ} (hm : detC m ≠ 0) {t : ℂ}
    (ht : t ≠ 0) (n : ℕ) :
    ‖𝓕 (fun x : ℂ => phiFam Q m x t) (F.fr t)‖ ≤ (F.c⁻¹ * ‖t‖) ^ n *
      (2 ^ n * ∑ j ∈ Finset.range (n + 1), ∫ x : ℂ, ‖iteratedFDeriv ℝ j (fun x => phiFam Q m x t) x‖) := by
  have hcpos : 0 < F.c := F.c_pos
  have h1 := hQ.fourier_slice_bound hm t n (F.fr t)
  calc ‖𝓕 (fun x : ℂ => phiFam Q m x t) (F.fr t)‖
      = (F.c⁻¹ * ‖t‖) ^ n * ‖F.fr t‖ ^ n * ‖𝓕 (fun x : ℂ => phiFam Q m x t) (F.fr t)‖ := by
        rw [unit_pow F ht n, one_mul]
    _ = (F.c⁻¹ * ‖t‖) ^ n * (‖F.fr t‖ ^ n * ‖𝓕 (fun x : ℂ => phiFam Q m x t) (F.fr t)‖) := mul_assoc _ _ _
    _ ≤ (F.c⁻¹ * ‖t‖) ^ n *
          (2 ^ n * ∑ j ∈ Finset.range (n + 1), ∫ x : ℂ, ‖iteratedFDeriv ℝ j (fun x => phiFam Q m x t) x‖) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)

open scoped FourierTransform in

private theorem
    innFC_bound (F : Freq) {Q : X₄ℂ → ℂ → ℂ → ℂ} (hQ : IsPoly Q) (n : ℕ) {R σ : ℝ} (hR : 0 ≤ R) (hσ : 0 < σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : X₄ℂ, detC m ≠ 0 → ‖m‖ ≤ R → (∀ x Y : ℂ, σ * (‖x‖ ^ 2 + ‖Y‖ ^ 2) ≤ qForm m x Y) →
      ∀ t : ℂ, ‖innFC F Q m t‖ ≤
        C * (‖t‖ ^ n * ‖t‖⁻¹ ^ 2) * Real.exp (-(2 * Real.pi * σ / 2) * ‖t‖ ^ 2) := by
  obtain ⟨K, hK, hKb⟩ := hQ.sum_integral_iteratedFDeriv_ball_bound n hR hσ
  have hcpos : 0 < F.c := F.c_pos
  refine ⟨|F.jac| * F.c⁻¹ ^ n * 2 ^ n * K, by positivity, fun m hm hmR hq t => ?_⟩
  by_cases ht : t = 0
  · subst ht
    simp [innFC]
  have hS := hKb m hmR hq t
  have hF := norm_fourier_slice_le F hQ hm ht n
  have hpre : 0 ≤ |F.jac| * ‖t‖⁻¹ ^ 2 := by positivity
  calc ‖innFC F Q m t‖ = |F.jac| * ‖t‖⁻¹ ^ 2 * ‖𝓕 (fun x : ℂ => phiFam Q m x t) (F.fr t)‖ := by
        rw [innFC, norm_mul, norm_innFC_prefactor]
    _ ≤ |F.jac| * ‖t‖⁻¹ ^ 2 * ((F.c⁻¹ * ‖t‖) ^ n *
          (2 ^ n * ∑ j ∈ Finset.range (n + 1), ∫ x : ℂ, ‖iteratedFDeriv ℝ j (fun x => phiFam Q m x t) x‖)) :=
        mul_le_mul_of_nonneg_left hF hpre
    _ ≤ |F.jac| * ‖t‖⁻¹ ^ 2 * ((F.c⁻¹ * ‖t‖) ^ n * (2 ^ n * (K * Real.exp (-(2 * Real.pi * σ / 2) * ‖t‖ ^ 2)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hS (by positivity))
          (by positivity)) hpre
    _ = |F.jac| * F.c⁻¹ ^ n * 2 ^ n * K * (‖t‖ ^ n * ‖t‖⁻¹ ^ 2) * Real.exp (-(2 * Real.pi * σ / 2) * ‖t‖ ^ 2) := by
        ring

open scoped FourierTransform in

private theorem innFC_gate_bound (F : Freq) {Q : X₄ℂ → ℂ → ℂ → ℂ} (hQ : IsPoly Q) (n : ℕ) :
    ∃ (C : ℝ) (d : ℕ), 0 ≤ C ∧ ∀ (ρ : ℝ) (m : X₄ℂ), IsGateC ρ m → ∀ t : ℂ,
      ‖innFC F Q m t‖ ≤ C * (‖t‖ ^ n * ‖t‖⁻¹ ^ 2) *
        ((1 + ‖t‖) ^ d * Real.exp (-(2 * Real.pi / 2) * (ρ * ‖t‖) ^ 2)) := by
  obtain ⟨K, d, hK, hKb⟩ := hQ.sum_integral_iteratedFDeriv_gate_bound n
  have hcpos : 0 < F.c := F.c_pos
  refine ⟨|F.jac| * F.c⁻¹ ^ n * 2 ^ n * K, d, by positivity, fun ρ m hg t => ?_⟩
  by_cases ht : t = 0
  · subst ht
    simp [innFC]
  have hS := hKb m ρ hg.bot hg.top hg.form t
  have hF := norm_fourier_slice_le F hQ hg.detC_ne ht n
  have hpre : 0 ≤ |F.jac| * ‖t‖⁻¹ ^ 2 := by positivity
  calc ‖innFC F Q m t‖ = |F.jac| * ‖t‖⁻¹ ^ 2 * ‖𝓕 (fun x : ℂ => phiFam Q m x t) (F.fr t)‖ := by
        rw [innFC, norm_mul, norm_innFC_prefactor]
    _ ≤ |F.jac| * ‖t‖⁻¹ ^ 2 * ((F.c⁻¹ * ‖t‖) ^ n *
          (2 ^ n * ∑ j ∈ Finset.range (n + 1), ∫ x : ℂ, ‖iteratedFDeriv ℝ j (fun x => phiFam Q m x t) x‖)) :=
        mul_le_mul_of_nonneg_left hF hpre
    _ ≤ |F.jac| * ‖t‖⁻¹ ^ 2 * ((F.c⁻¹ * ‖t‖) ^ n *
          (2 ^ n * (K * (1 + ‖t‖) ^ d * Real.exp (-(2 * Real.pi / 2) * (ρ * ‖t‖) ^ 2)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hS (by positivity))
          (by positivity)) hpre
    _ = |F.jac| * F.c⁻¹ ^ n * 2 ^ n * K * (‖t‖ ^ n * ‖t‖⁻¹ ^ 2) *
          ((1 + ‖t‖) ^ d * Real.exp (-(2 * Real.pi / 2) * (ρ * ‖t‖) ^ 2)) := by
        ring

end IsPoly

private theorem
    weight_mul {r : ℝ} (hr : r ≠ 0) (A : ℕ) : (r ^ A + r⁻¹ ^ A) * (r ^ (A + 2) * r⁻¹ ^ 2) = 1 + r ^ (2 * A) := by
  have h1 : r ^ (A + 2) * r⁻¹ ^ 2 = r ^ A := by
    rw [pow_add, mul_assoc, ← mul_pow, mul_inv_cancel₀ hr, one_pow, mul_one]
  have h2 : r⁻¹ ^ A * r ^ A = 1 := by rw [← mul_pow, inv_mul_cancel₀ hr, one_pow]
  rw [h1, add_mul, h2]
  ring

private theorem norm_pow_le_one_add_pow (r : ℝ) (hr : 0 ≤ r) (k : ℕ) : r ^ k ≤ (1 + r ^ 2) ^ k := by
  have h : r ≤ 1 + r ^ 2 := by nlinarith [sq_nonneg (r - 1)]
  exact pow_le_pow_left₀ hr h k

open MeasureTheory in

private theorem integrable_one_add_norm_pow_mul_exp {c : ℝ} (hc : 0 < c) (k : ℕ) :
    Integrable fun t : ℂ => (1 + ‖t‖ ^ k) * Real.exp (-c * ‖t‖ ^ 2) := by
  obtain ⟨K, hK, habs⟩ := one_add_pow_le_exp k (c := c / 2) (by positivity)
  have hc2 : 0 < c / 2 := by positivity
  refine ((integrable_exp_neg_mul_norm_sq hc2).const_mul (2 * K)).mono' ?_ (Filter.Eventually.of_forall fun t => ?_)
  · exact ((continuous_const.add (continuous_norm.pow k)).mul (by fun_prop)).aestronglyMeasurable
  · have h0 : 0 ≤ ‖t‖ ^ 2 := by positivity
    have h1 : ‖t‖ ^ k ≤ (1 + ‖t‖ ^ 2) ^ k := norm_pow_le_one_add_pow ‖t‖ (norm_nonneg t) k
    have h2 : (1 + ‖t‖ ^ 2) ^ k ≤ K * Real.exp (c / 2 * ‖t‖ ^ 2) := habs _ h0
    have h3 : (1 : ℝ) ≤ (1 + ‖t‖ ^ 2) ^ k := one_le_pow₀ (by linarith)
    have he := Real.exp_pos (-c * ‖t‖ ^ 2)
    have hsplit := exp_mul_exp_half c (‖t‖ ^ 2)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc (1 + ‖t‖ ^ k) * Real.exp (-c * ‖t‖ ^ 2)
        ≤ (2 * (K * Real.exp (c / 2 * ‖t‖ ^ 2))) * Real.exp (-c * ‖t‖ ^ 2) := by
          refine mul_le_mul_of_nonneg_right ?_ he.le
          linarith
      _ = 2 * K * Real.exp (-(c / 2) * ‖t‖ ^ 2) := by
          rw [← hsplit]
          ring

open MeasureTheory in
private theorem ae_ne_zero_C : ∀ᵐ t : ℂ, t ≠ 0 := by
  have h : ∀ᵐ t : ℂ, t ∈ ({0}ᶜ : Set ℂ) := by
    exact compl_mem_ae_iff.mpr (measure_singleton 0)
  exact h.mono fun t ht => Set.mem_compl_singleton_iff.mp ht

open MeasureTheory in

private def tIntC (F : Freq) (Q : X₄ℂ → ℂ → ℂ → ℂ) (χ : ℂ → ℂ) (m : X₄ℂ) : ℂ := ∫ t : ℂ, χ t * innFC F Q m t

namespace IsPoly

open MeasureTheory in

private theorem integrable_chi_mul_innFC (F : Freq) {Q : X₄ℂ → ℂ → ℂ → ℂ} (hQ : IsPoly Q) {m : X₄ℂ} (hm : detC m ≠ 0)
    {χ : ℂ → ℂ} (hχ : Measurable χ) {A : ℕ} (hχA : ∀ t : ℂ, t ≠ 0 → ‖χ t‖ ≤ ‖t‖ ^ A + ‖t‖⁻¹ ^ A) :
    Integrable fun t : ℂ => χ t * innFC F Q m t := by
  obtain ⟨σ, hσ, hev⟩ := eventually_qForm_ge hm
  have hq : ∀ x Y : ℂ, σ * (‖x‖ ^ 2 + ‖Y‖ ^ 2) ≤ qForm m x Y := hev.self_of_nhds
  obtain ⟨C, hC0, hCb⟩ := hQ.innFC_bound F (A + 2) (norm_nonneg m) hσ
  have hc : 0 < 2 * Real.pi * σ / 2 := by positivity
  refine ((integrable_one_add_norm_pow_mul_exp hc (2 * A)).const_mul C).mono'
    (hχ.mul (hQ.measurable_innFC F m)).aestronglyMeasurable (ae_ne_zero_C.mono fun t ht => ?_)
  have hr : ‖t‖ ≠ 0 := norm_ne_zero_iff.mpr ht
  have hw0 : 0 ≤ ‖t‖ ^ A + ‖t‖⁻¹ ^ A := by positivity
  calc ‖χ t * innFC F Q m t‖ = ‖χ t‖ * ‖innFC F Q m t‖ := norm_mul _ _
    _ ≤ (‖t‖ ^ A + ‖t‖⁻¹ ^ A) *
          (C * (‖t‖ ^ (A + 2) * ‖t‖⁻¹ ^ 2) * Real.exp (-(2 * Real.pi * σ / 2) * ‖t‖ ^ 2)) :=
        mul_le_mul (hχA t ht) (hCb m hm le_rfl hq t) (norm_nonneg _) hw0
    _ = C * ((‖t‖ ^ A + ‖t‖⁻¹ ^ A) * (‖t‖ ^ (A + 2) * ‖t‖⁻¹ ^ 2) * Real.exp (-(2 * Real.pi * σ / 2) * ‖t‖ ^ 2)) := by
        ring
    _ = C * ((1 + ‖t‖ ^ (2 * A)) * Real.exp (-(2 * Real.pi * σ / 2) * ‖t‖ ^ 2)) := by rw [weight_mul hr]

end IsPoly

private def sumFormₗ : ((Fin 2 → Fin 2 → ℂ) × (Fin 2 → Fin 2 → ℂ)) →ₗ[ℝ] (X₄ℂ →L[ℝ] ℂ) where
  toFun p := sumForm p.1 p.2
  map_add' p q := by
    refine ContinuousLinearMap.ext fun v => ?_
    simp only [ContinuousLinearMap.add_apply, sumForm_apply, Fin.sum_univ_two, Prod.fst_add, Prod.snd_add,
      Pi.add_apply]
    ring
  map_smul' r p := by
    refine ContinuousLinearMap.ext fun v => ?_
    simp only [ContinuousLinearMap.smul_apply, sumForm_apply, Fin.sum_univ_two, Prod.smul_fst, Prod.smul_snd,
      Pi.smul_apply, RingHom.id_apply, Complex.real_smul]
    ring

private def sumFormL : ((Fin 2 → Fin 2 → ℂ) × (Fin 2 → Fin 2 → ℂ)) →L[ℝ] (X₄ℂ →L[ℝ] ℂ) :=
  LinearMap.toContinuousLinearMap sumFormₗ

@[scoped simp] private theorem sumFormL_apply (c c' : Fin 2 → Fin 2 → ℂ) : sumFormL (c, c') = sumForm c c' := rfl

private theorem sumFormL_apply' (p : (Fin 2 → Fin 2 → ℂ) × (Fin 2 → Fin 2 → ℂ)) : sumFormL p = sumForm p.1 p.2 := rfl

private theorem smul_sumForm (a : ℂ) (c c' : Fin 2 → Fin 2 → ℂ) :
    a • sumForm c c' = sumForm (fun i j => a * c i j) fun i j => a * c' i j := by
  refine ContinuousLinearMap.ext fun v => ?_
  simp only [ContinuousLinearMap.smul_apply, sumForm_apply, Fin.sum_univ_two, smul_eq_mul]
  ring

private theorem norm_sumForm_le (c c' : Fin 2 → Fin 2 → ℂ) :
    ‖sumForm c c'‖ ≤ ∑ i : Fin 2, ∑ j : Fin 2, (‖c i j‖ + ‖c' i j‖) := by
  refine ContinuousLinearMap.opNorm_le_bound _
    (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => add_nonneg (norm_nonneg _) (norm_nonneg _)) fun v => ?_
  rw [sumForm_apply, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  calc ‖c i j * v i j + c' i j * conj (v i j)‖ ≤ ‖c i j‖ * ‖v i j‖ + ‖c' i j‖ * ‖v i j‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, norm_mul, Complex.norm_conj]
    _ ≤ ‖c i j‖ * ‖v‖ + ‖c' i j‖ * ‖v‖ :=
        add_le_add (mul_le_mul_of_nonneg_left (entry_norm_le_norm v i j) (norm_nonneg _))
          (mul_le_mul_of_nonneg_left (entry_norm_le_norm v i j) (norm_nonneg _))
    _ = (‖c i j‖ + ‖c' i j‖) * ‖v‖ := by ring

private theorem continuous_sumForm_comp {c c' : ℂ → Fin 2 → Fin 2 → ℂ} (hc : ∀ i j, Continuous fun x => c x i j)
    (hc' : ∀ i j, Continuous fun x => c' x i j) : Continuous fun x => sumForm (c x) (c' x) := by
  have h1 : Continuous c := continuous_pi fun i => continuous_pi fun j => hc i j
  have h2 : Continuous c' := continuous_pi fun i => continuous_pi fun j => hc' i j
  have h : Continuous fun x => (c x, c' x) := h1.prodMk h2
  simpa [Function.comp_def] using sumFormL.continuous.comp h

open MeasureTheory in
private theorem integral_sumForm {c c' : ℂ → Fin 2 → Fin 2 → ℂ} (hc : ∀ i j, Integrable fun x => c x i j)
    (hc' : ∀ i j, Integrable fun x => c' x i j) :
    ∫ x : ℂ, sumForm (c x) (c' x) = sumForm (fun i j => ∫ x : ℂ, c x i j) fun i j => ∫ x : ℂ, c' x i j := by
  have hci : ∀ i, Integrable fun x => c x i := fun i => integrable_pi_iff.2 fun j => hc i j
  have hci' : ∀ i, Integrable fun x => c' x i := fun i => integrable_pi_iff.2 fun j => hc' i j
  have hint : Integrable c := integrable_pi_iff.2 hci
  have hint' : Integrable c' := integrable_pi_iff.2 hci'
  have hpair : Integrable fun x => (c x, c' x) := hint.prodMk hint'
  have h := sumFormL.integral_comp_comm hpair
  simp only [sumFormL_apply', integral_pair hint hint'] at h
  rw [h]
  congr 1
  · funext i j
    rw [eval_integral hci i, eval_integral (fun j => hc i j) j]
  · funext i j
    rw [eval_integral hci' i, eval_integral (fun j => hc' i j) j]

private theorem contDiffOn_of_sumForm_closed (𝓟 : (X₄ℂ → ℂ) → Prop) {s : Set X₄ℂ} (hs : IsOpen s)
    (hclosed : ∀ f, 𝓟 f → ∃ D D' : Fin 2 → Fin 2 → X₄ℂ → ℂ, (∀ i j, 𝓟 (D i j)) ∧ (∀ i j, 𝓟 (D' i j)) ∧
      ∀ m ∈ s, HasFDerivAt f (sumForm (fun i j => D i j m) fun i j => D' i j m) m) :
    ∀ f, 𝓟 f → ContDiffOn ℝ (⊤ : ℕ∞) f s := by
  have H : ∀ n : ℕ, ∀ f, 𝓟 f → ContDiffOn ℝ n f s := by
    intro n
    induction n with
    | zero =>
      intro f hf
      obtain ⟨D, D', -, -, hD⟩ := hclosed f hf
      rw [Nat.cast_zero, contDiffOn_zero]
      exact fun m hm => (hD m hm).continuousAt.continuousWithinAt
    | succ n ih =>
      intro f hf
      obtain ⟨D, D', hDP, hDP', hD⟩ := hclosed f hf
      rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen hs]
      refine ⟨fun m hm => (hD m hm).differentiableAt.differentiableWithinAt, by simp, ?_⟩
      have h₁ : ContDiffOn ℝ n (fun m => fun i j => D i j m) s :=
        contDiffOn_pi.2 fun i => contDiffOn_pi.2 fun j => ih (D i j) (hDP i j)
      have h₂ : ContDiffOn ℝ n (fun m => fun i j => D' i j m) s :=
        contDiffOn_pi.2 fun i => contDiffOn_pi.2 fun j => ih (D' i j) (hDP' i j)
      have hDs : ContDiffOn ℝ n (fun m => sumFormL (fun i j => D i j m, fun i j => D' i j m)) s :=
        sumFormL.contDiff.comp_contDiffOn (h₁.prodMk h₂)
      refine hDs.congr fun m hm => ?_
      rw [(hD m hm).fderiv, sumFormL_apply]
  intro f hf
  exact contDiffOn_infty.2 fun n => H n f hf

private def fkerC (ξ x : ℂ) : ℂ := Complex.exp (((-2 * Real.pi * inner ℝ x ξ : ℝ) : ℂ) * Complex.I)

private theorem norm_fkerC (ξ x : ℂ) : ‖fkerC ξ x‖ = 1 := by
  rw [fkerC]
  exact Complex.norm_exp_ofReal_mul_I _

private theorem continuous_fkerC (ξ : ℂ) : Continuous (fkerC ξ) := by
  unfold fkerC
  fun_prop

open scoped FourierTransform in
private theorem fourier_eq_C (g : ℂ → ℂ) (ξ : ℂ) : 𝓕 g ξ = ∫ x : ℂ, fkerC ξ x * g x := by
  rw [Real.fourier_eq']
  simp only [smul_eq_mul, fkerC]

namespace IsPoly

open MeasureTheory in
private theorem integrable_fkerC_mul {Q : X₄ℂ → ℂ → ℂ → ℂ} (hQ : IsPoly Q) {m : X₄ℂ} (hm : detC m ≠ 0) (Y ξ : ℂ) :
    Integrable fun x : ℂ => fkerC ξ x * phiFam Q m x Y := by
  refine (hQ.integrable_phiFam hm Y).norm.mono' ?_ ?_
  · exact ((continuous_fkerC ξ).mul (hQ.contDiff_x_phiFam m Y).continuous).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun x => ?_
    exact (show ‖fkerC ξ x * phiFam Q m x Y‖ = ‖phiFam Q m x Y‖ by rw [norm_mul, norm_fkerC, one_mul]).le

open MeasureTheory in
open scoped FourierTransform in

private theorem hasFDerivAt_fourier_slice {P : X₄ℂ → ℂ → ℂ → ℂ} (h : IsPoly P) :
    ∃ D D' : Fin 2 → Fin 2 → X₄ℂ → ℂ → ℂ → ℂ, (∀ i j, IsPoly (D i j)) ∧ (∀ i j, IsPoly (D' i j)) ∧
      ∀ m₀ : X₄ℂ, detC m₀ ≠ 0 → ∀ Y ξ : ℂ,
        HasFDerivAt (fun m => 𝓕 (fun x => phiFam P m x Y) ξ)
          (sumForm (fun i j => 𝓕 (fun x => phiFam (D i j) m₀ x Y) ξ) fun i j => 𝓕 (fun x => phiFam (D' i j) m₀ x Y) ξ)
          m₀ := by
  obtain ⟨D, D', hD, hD', hderiv⟩ := h.hasFDerivAt_m_phiFam
  refine ⟨D, D', hD, hD', fun m₀ hm₀ Y ξ => ?_⟩
  obtain ⟨σ, hσ, hev⟩ := eventually_qForm_ge hm₀
  have hnorm : ∀ᶠ m in nhds m₀, ‖m‖ < ‖m₀‖ + 1 :=
    continuous_norm.continuousAt.eventually_lt continuousAt_const (by linarith : ‖m₀‖ < ‖m₀‖ + 1)
  have hs : {m : X₄ℂ | ‖m‖ < ‖m₀‖ + 1 ∧ ∀ x Y : ℂ, σ * (‖x‖ ^ 2 + ‖Y‖ ^ 2) ≤ qForm m x Y} ∈ nhds m₀ :=
    hnorm.and hev
  have hR : (0 : ℝ) ≤ ‖m₀‖ + 1 := by positivity
  choose K _hK hKb using fun i j => (hD i j).phiFam_bound hR hσ
  choose K' _hK' hKb' using fun i j => (hD' i j).phiFam_bound hR hσ
  have hc : 0 < 2 * Real.pi * σ / 2 := by positivity
  have e : (fun m => 𝓕 (fun x => phiFam P m x Y) ξ) = fun m => ∫ x : ℂ, fkerC ξ x * phiFam P m x Y :=
    funext fun m => fourier_eq_C _ _
  rw [e]
  have hcont : Continuous fun x => sumForm (fun i j => phiFam (D i j) m₀ x Y) fun i j => phiFam (D' i j) m₀ x Y :=
    continuous_sumForm_comp (fun i j => ((hD i j).contDiff_x_phiFam m₀ Y).continuous)
      fun i j => ((hD' i j).contDiff_x_phiFam m₀ Y).continuous
  have hsplit : ∀ x : ℂ, Real.exp (-(2 * Real.pi * σ / 2) * (‖x‖ ^ 2 + ‖Y‖ ^ 2)) =
      Real.exp (-(2 * Real.pi * σ / 2) * ‖Y‖ ^ 2) * Real.exp (-(2 * Real.pi * σ / 2) * ‖x‖ ^ 2) := fun x => by
    rw [← Real.exp_add]
    congr 1
    ring
  have hbd : ∀ᵐ x : ℂ, ∀ m ∈ {m : X₄ℂ | ‖m‖ < ‖m₀‖ + 1 ∧ ∀ x Y : ℂ, σ * (‖x‖ ^ 2 + ‖Y‖ ^ 2) ≤ qForm m x Y},
      ‖fkerC ξ x • sumForm (fun i j => phiFam (D i j) m x Y) fun i j => phiFam (D' i j) m x Y‖ ≤
        (∑ i : Fin 2, ∑ j : Fin 2, (K i j + K' i j)) * Real.exp (-(2 * Real.pi * σ / 2) * ‖Y‖ ^ 2) *
          Real.exp (-(2 * Real.pi * σ / 2) * ‖x‖ ^ 2) := by
    refine Filter.Eventually.of_forall fun x m hm => ?_
    obtain ⟨hm1, hm2⟩ := hm
    rw [norm_smul, norm_fkerC, one_mul]
    refine (norm_sumForm_le _ _).trans ?_
    have hb : ∀ i j, ‖phiFam (D i j) m x Y‖ ≤
        K i j * (Real.exp (-(2 * Real.pi * σ / 2) * ‖Y‖ ^ 2) * Real.exp (-(2 * Real.pi * σ / 2) * ‖x‖ ^ 2)) :=
      fun i j => by
        rw [← hsplit]
        exact hKb i j m hm1.le hm2 x Y
    have hb' : ∀ i j, ‖phiFam (D' i j) m x Y‖ ≤
        K' i j * (Real.exp (-(2 * Real.pi * σ / 2) * ‖Y‖ ^ 2) * Real.exp (-(2 * Real.pi * σ / 2) * ‖x‖ ^ 2)) :=
      fun i j => by
        rw [← hsplit]
        exact hKb' i j m hm1.le hm2 x Y
    simp only [Fin.sum_univ_two]
    linarith [hb 0 0, hb 0 1, hb 1 0, hb 1 1, hb' 0 0, hb' 0 1, hb' 1 0, hb' 1 1]
  have hbi : Integrable fun x : ℂ => (∑ i : Fin 2, ∑ j : Fin 2, (K i j + K' i j)) *
      Real.exp (-(2 * Real.pi * σ / 2) * ‖Y‖ ^ 2) * Real.exp (-(2 * Real.pi * σ / 2) * ‖x‖ ^ 2) :=
    (integrable_exp_neg_mul_norm_sq hc).const_mul _
  have hdf : ∀ᵐ x : ℂ, ∀ m ∈ {m : X₄ℂ | ‖m‖ < ‖m₀‖ + 1 ∧ ∀ x Y : ℂ, σ * (‖x‖ ^ 2 + ‖Y‖ ^ 2) ≤ qForm m x Y},
      HasFDerivAt (fun m => fkerC ξ x * phiFam P m x Y)
        (fkerC ξ x • sumForm (fun i j => phiFam (D i j) m x Y) fun i j => phiFam (D' i j) m x Y) m :=
    Filter.Eventually.of_forall fun x m _ => (hderiv m x Y).const_mul (fkerC ξ x)
  refine (hasFDerivAt_integral_of_dominated_of_fderiv_le hs ?_ ?_ ?_ hbd hbi hdf).congr_fderiv ?_
  · exact Filter.Eventually.of_forall fun m =>
      ((continuous_fkerC ξ).mul (h.contDiff_x_phiFam m Y).continuous).aestronglyMeasurable
  · exact h.integrable_fkerC_mul hm₀ Y ξ
  · exact ((continuous_fkerC ξ).smul hcont).aestronglyMeasurable
  · simp_rw [smul_sumForm]
    rw [integral_sumForm (fun i j => (hD i j).integrable_fkerC_mul hm₀ Y ξ)
      fun i j => (hD' i j).integrable_fkerC_mul hm₀ Y ξ]
    simp_rw [fourier_eq_C]

private theorem hasFDerivAt_innFC (F : Freq) {P : X₄ℂ → ℂ → ℂ → ℂ} (h : IsPoly P) :
    ∃ D D' : Fin 2 → Fin 2 → X₄ℂ → ℂ → ℂ → ℂ, (∀ i j, IsPoly (D i j)) ∧ (∀ i j, IsPoly (D' i j)) ∧
      ∀ m₀ : X₄ℂ, detC m₀ ≠ 0 → ∀ t : ℂ,
        HasFDerivAt (fun m => innFC F P m t)
          (sumForm (fun i j => innFC F (D i j) m₀ t) fun i j => innFC F (D' i j) m₀ t) m₀ := by
  obtain ⟨D, D', hD, hD', hF⟩ := h.hasFDerivAt_fourier_slice
  refine ⟨D, D', hD, hD', fun m₀ hm₀ t => ?_⟩
  unfold innFC
  refine ((hF m₀ hm₀ t (F.fr t)).const_mul ((F.jac * ‖t‖⁻¹ ^ 2 : ℝ) : ℂ)).congr_fderiv ?_
  rw [smul_sumForm]

end IsPoly

namespace IsPoly

open MeasureTheory in

private theorem
    hasFDerivAt_tIntC (F : Freq) {Q : X₄ℂ → ℂ → ℂ → ℂ} (hQ : IsPoly Q) {χ : ℂ → ℂ} (hχ : Measurable χ) {A : ℕ}
    (hχA : ∀ t : ℂ, t ≠ 0 → ‖χ t‖ ≤ ‖t‖ ^ A + ‖t‖⁻¹ ^ A) :
    ∃ D D' : Fin 2 → Fin 2 → X₄ℂ → ℂ → ℂ → ℂ, (∀ i j, IsPoly (D i j)) ∧ (∀ i j, IsPoly (D' i j)) ∧
      ∀ m₀ : X₄ℂ, detC m₀ ≠ 0 →
        HasFDerivAt (fun m => tIntC F Q χ m)
          (sumForm (fun i j => tIntC F (D i j) χ m₀) fun i j => tIntC F (D' i j) χ m₀) m₀ := by
  obtain ⟨D, D', hD, hD', hinn⟩ := hQ.hasFDerivAt_innFC F
  refine ⟨D, D', hD, hD', fun m₀ hm₀ => ?_⟩
  simp only [tIntC]
  obtain ⟨σ, hσ, hev⟩ := eventually_qForm_ge hm₀
  have hnorm : ∀ᶠ m in nhds m₀, ‖m‖ < ‖m₀‖ + 1 :=
    continuous_norm.continuousAt.eventually_lt continuousAt_const (by linarith : ‖m₀‖ < ‖m₀‖ + 1)
  have hdet : ∀ᶠ m in nhds m₀, detC m ≠ 0 := continuous_detC.continuousAt.eventually_ne hm₀
  have hs : {m : X₄ℂ | ‖m‖ < ‖m₀‖ + 1 ∧ (∀ x Y : ℂ, σ * (‖x‖ ^ 2 + ‖Y‖ ^ 2) ≤ qForm m x Y) ∧ detC m ≠ 0} ∈
      nhds m₀ :=
    hnorm.and (hev.and hdet)
  have hR : (0 : ℝ) ≤ ‖m₀‖ + 1 := by positivity
  choose C _hC0 hCb using fun i j => (hD i j).innFC_bound F (A + 2) hR hσ
  choose C' _hC0' hCb' using fun i j => (hD' i j).innFC_bound F (A + 2) hR hσ
  have hc : 0 < 2 * Real.pi * σ / 2 := by positivity
  have hbd : ∀ᵐ t : ℂ,
      ∀ m ∈ {m : X₄ℂ | ‖m‖ < ‖m₀‖ + 1 ∧ (∀ x Y : ℂ, σ * (‖x‖ ^ 2 + ‖Y‖ ^ 2) ≤ qForm m x Y) ∧ detC m ≠ 0},
      ‖χ t • sumForm (fun i j => innFC F (D i j) m t) fun i j => innFC F (D' i j) m t‖ ≤
        (∑ i : Fin 2, ∑ j : Fin 2, (C i j + C' i j)) *
          ((1 + ‖t‖ ^ (2 * A)) * Real.exp (-(2 * Real.pi * σ / 2) * ‖t‖ ^ 2)) := by
    refine ae_ne_zero_C.mono fun t ht m hm => ?_
    obtain ⟨hm1, hm2, hm3⟩ := hm
    have hr : ‖t‖ ≠ 0 := norm_ne_zero_iff.mpr ht
    have hw0 : 0 ≤ ‖t‖ ^ A + ‖t‖⁻¹ ^ A := by positivity
    have hb : ∀ i j, ‖innFC F (D i j) m t‖ ≤
        C i j * (‖t‖ ^ (A + 2) * ‖t‖⁻¹ ^ 2) * Real.exp (-(2 * Real.pi * σ / 2) * ‖t‖ ^ 2) :=
      fun i j => hCb i j m hm3 hm1.le hm2 t
    have hb' : ∀ i j, ‖innFC F (D' i j) m t‖ ≤
        C' i j * (‖t‖ ^ (A + 2) * ‖t‖⁻¹ ^ 2) * Real.exp (-(2 * Real.pi * σ / 2) * ‖t‖ ^ 2) :=
      fun i j => hCb' i j m hm3 hm1.le hm2 t
    have hsum : ‖sumForm (fun i j => innFC F (D i j) m t) fun i j => innFC F (D' i j) m t‖ ≤
        (∑ i : Fin 2, ∑ j : Fin 2, (C i j + C' i j)) *
          ((‖t‖ ^ (A + 2) * ‖t‖⁻¹ ^ 2) * Real.exp (-(2 * Real.pi * σ / 2) * ‖t‖ ^ 2)) := by
      refine (norm_sumForm_le _ _).trans ?_
      simp only [Fin.sum_univ_two]
      linarith [hb 0 0, hb 0 1, hb 1 0, hb 1 1, hb' 0 0, hb' 0 1, hb' 1 0, hb' 1 1]
    calc ‖χ t • sumForm (fun i j => innFC F (D i j) m t) fun i j => innFC F (D' i j) m t‖
        = ‖χ t‖ * ‖sumForm (fun i j => innFC F (D i j) m t) fun i j => innFC F (D' i j) m t‖ := norm_smul _ _
      _ ≤ (‖t‖ ^ A + ‖t‖⁻¹ ^ A) *
            ((∑ i : Fin 2, ∑ j : Fin 2, (C i j + C' i j)) *
              ((‖t‖ ^ (A + 2) * ‖t‖⁻¹ ^ 2) * Real.exp (-(2 * Real.pi * σ / 2) * ‖t‖ ^ 2))) :=
          mul_le_mul (hχA t ht) hsum (norm_nonneg _) hw0
      _ = (∑ i : Fin 2, ∑ j : Fin 2, (C i j + C' i j)) *
            ((‖t‖ ^ A + ‖t‖⁻¹ ^ A) * (‖t‖ ^ (A + 2) * ‖t‖⁻¹ ^ 2) *
              Real.exp (-(2 * Real.pi * σ / 2) * ‖t‖ ^ 2)) := by ring
      _ = (∑ i : Fin 2, ∑ j : Fin 2, (C i j + C' i j)) *
            ((1 + ‖t‖ ^ (2 * A)) * Real.exp (-(2 * Real.pi * σ / 2) * ‖t‖ ^ 2)) := by
          rw [weight_mul hr]
  have hbi : Integrable fun t : ℂ =>
      (∑ i : Fin 2, ∑ j : Fin 2, (C i j + C' i j)) *
        ((1 + ‖t‖ ^ (2 * A)) * Real.exp (-(2 * Real.pi * σ / 2) * ‖t‖ ^ 2)) :=
    (integrable_one_add_norm_pow_mul_exp hc (2 * A)).const_mul _
  have hdf : ∀ᵐ t : ℂ,
      ∀ m ∈ {m : X₄ℂ | ‖m‖ < ‖m₀‖ + 1 ∧ (∀ x Y : ℂ, σ * (‖x‖ ^ 2 + ‖Y‖ ^ 2) ≤ qForm m x Y) ∧ detC m ≠ 0},
      HasFDerivAt (fun m => χ t * innFC F Q m t)
        (χ t • sumForm (fun i j => innFC F (D i j) m t) fun i j => innFC F (D' i j) m t) m :=
    Filter.Eventually.of_forall fun t m hm => by
      obtain ⟨-, -, hm3⟩ := hm
      exact (hinn m hm3 t).const_mul (χ t)
  have hpi : AEStronglyMeasurable (fun t : ℂ => fun i j : Fin 2 => innFC F (D i j) m₀ t) volume :=
    (measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => (hD i j).measurable_innFC F m₀).aestronglyMeasurable
  have hpi' : AEStronglyMeasurable (fun t : ℂ => fun i j : Fin 2 => innFC F (D' i j) m₀ t) volume :=
    (measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => (hD' i j).measurable_innFC F m₀).aestronglyMeasurable
  have hpair : AEStronglyMeasurable
      (fun t : ℂ => ((fun i j : Fin 2 => innFC F (D i j) m₀ t), fun i j : Fin 2 => innFC F (D' i j) m₀ t)) volume :=
    hpi.prodMk hpi'
  have hsum_ae : AEStronglyMeasurable
      (fun t : ℂ => sumForm (fun i j => innFC F (D i j) m₀ t) fun i j => innFC F (D' i j) m₀ t) volume := by
    simpa using sumFormL.continuous.comp_aestronglyMeasurable hpair
  refine (hasFDerivAt_integral_of_dominated_of_fderiv_le hs ?_ ?_ ?_ hbd hbi hdf).congr_fderiv ?_
  · exact Filter.Eventually.of_forall fun m => (hχ.mul (hQ.measurable_innFC F m)).aestronglyMeasurable
  · exact hQ.integrable_chi_mul_innFC F hm₀ hχ hχA
  · exact hχ.aestronglyMeasurable.smul hsum_ae
  · simp_rw [smul_sumForm]
    rw [integral_sumForm (fun i j => (hD i j).integrable_chi_mul_innFC F hm₀ hχ hχA)
      fun i j => (hD' i j).integrable_chi_mul_innFC F hm₀ hχ hχA]

end IsPoly

section IteratedDerivativeBounds

open Set

namespace DerivEngine

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable {β : Type*} [Fintype β] {ι : Type*}

private noncomputable def coordL (b : Module.Basis β ℝ X) (k : β) : X →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap (b.coord k)

omit [Fintype β] in
private theorem coordL_apply (b : Module.Basis β ℝ X) (k : β) (v : X) : coordL b k v = b.repr v k := by
  simp [coordL]

private theorem fderiv_eq_sum (b : Module.Basis β ℝ X) (f : X → ℂ) (y : X) :
    fderiv ℝ f y =
      ∑ k, ContinuousLinearMap.smulRightL ℝ X ℂ (coordL b k) (fderiv ℝ f y (b k)) := by
  refine ContinuousLinearMap.ext fun v => ?_
  rw [ContinuousLinearMap.sum_apply]
  simp only [ContinuousLinearMap.smulRightL_apply_apply, ContinuousLinearMap.smulRight_apply, coordL_apply]
  conv_lhs => rw [← b.sum_repr v, map_sum]
  simp only [map_smul]

private theorem iteratedFDerivWithin_bound_of_closed (b : Module.Basis β ℝ X) (s : Set X) (hs : IsOpen s)
    (pt : ι → X) (hpt : ∀ i, pt i ∈ s) (φ : ℕ → ι → ℝ) (hφ0 : ∀ m i, 0 ≤ φ m i) (hφ : Monotone φ)
    (𝓟 : (X → ℂ) → Prop) (hsmooth : ∀ f, 𝓟 f → ContDiffOn ℝ (⊤ : ℕ∞) f s)
    (hderiv : ∀ f, 𝓟 f → ∀ k : β, 𝓟 (fun x => fderiv ℝ f x (b k)))
    (hbound : ∀ f, 𝓟 f → ∃ (C : ℝ) (m : ℕ), ∀ i, ‖f (pt i)‖ ≤ C * φ m i) :
    ∀ (j : ℕ) (f : X → ℂ), 𝓟 f →
      ∃ (C : ℝ) (m : ℕ), ∀ i, ‖iteratedFDerivWithin ℝ j f s (pt i)‖ ≤ C * φ m i := by
  suffices H : ∀ (j : ℕ) (f : X → ℂ), 𝓟 f → ∃ (C : ℝ) (m : ℕ), 0 ≤ C ∧
      ∀ i, ‖iteratedFDerivWithin ℝ j f s (pt i)‖ ≤ C * φ m i by
    intro j f hf
    obtain ⟨C, m, -, h⟩ := H j f hf
    exact ⟨C, m, h⟩
  have hsU : UniqueDiffOn ℝ s := hs.uniqueDiffOn
  intro j
  induction j with
  | zero =>
    intro f hf
    obtain ⟨C, m, h⟩ := hbound f hf
    refine ⟨max C 0, m, le_max_right _ _, fun i => ?_⟩
    rw [norm_iteratedFDerivWithin_zero]
    exact (h i).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hφ0 m i))
  | succ j ih =>
    intro f hf
    choose C m hC0 hCm using fun k : β => ih _ (hderiv f hf k)
    refine ⟨∑ k, ‖ContinuousLinearMap.smulRightL ℝ X ℂ (coordL b k)‖ * C k, Finset.univ.sup m,
      Finset.sum_nonneg fun k _ =>
        mul_nonneg (norm_nonneg (ContinuousLinearMap.smulRightL ℝ X ℂ (coordL b k))) (hC0 k), fun i => ?_⟩
    have hx : pt i ∈ s := hpt i
    have hj : (j : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top
    have hg : ∀ k : β, ContDiffWithinAt ℝ j (fun x => fderiv ℝ f x (b k)) s (pt i) := fun k =>
      ((hsmooth _ (hderiv f hf k)).contDiffWithinAt hx).of_le hj
    have hEq : EqOn (fderivWithin ℝ f s)
        (∑ k, ContinuousLinearMap.smulRightL ℝ X ℂ (coordL b k) ∘ fun x => fderiv ℝ f x (b k)) s := by
      intro y hy
      rw [fderivWithin_of_isOpen hs hy, fderiv_eq_sum b f y]
      simp only [Finset.sum_apply, Function.comp_apply]
    rw [← norm_iteratedFDerivWithin_fderivWithin hsU hx, iteratedFDerivWithin_congr hEq hx,
      iteratedFDerivWithin_sum_apply hsU hx
        (fun k _ => (ContinuousLinearMap.smulRightL ℝ X ℂ (coordL b k)).contDiff.comp_contDiffWithinAt (hg k))]
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun k _ => ?_
    rw [(ContinuousLinearMap.smulRightL ℝ X ℂ (coordL b k)).iteratedFDerivWithin_comp_left (hg k) hsU hx
      le_rfl, mul_assoc]
    refine (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    calc ‖iteratedFDerivWithin ℝ j (fun x => fderiv ℝ f x (b k)) s (pt i)‖
        ≤ C k * φ (m k) i := hCm k i
      _ ≤ C k * φ (Finset.univ.sup m) i :=
        mul_le_mul_of_nonneg_left (hφ (Finset.le_sup (f := m) (Finset.mem_univ k)) i) (hC0 k)

end DerivEngine

end IteratedDerivativeBounds

private def AgreesWith (𝓠 : (X₄ℂ → ℂ) → Prop) (s : Set X₄ℂ) (f : X₄ℂ → ℂ) : Prop := ∃ q, 𝓠 q ∧ Set.EqOn f q s

private def SumFormClosed (𝓠 : (X₄ℂ → ℂ) → Prop) (s : Set X₄ℂ) : Prop :=
  ∀ q, 𝓠 q → ∃ D D' : Fin 2 → Fin 2 → X₄ℂ → ℂ, (∀ i j, 𝓠 (D i j)) ∧ (∀ i j, 𝓠 (D' i j)) ∧
    ∀ m ∈ s, HasFDerivAt q (sumForm (fun i j => D i j m) fun i j => D' i j m) m

private def CombClosed (𝓠 : (X₄ℂ → ℂ) → Prop) : Prop :=
  ∀ D D' : Fin 2 → Fin 2 → X₄ℂ → ℂ, (∀ i j, 𝓠 (D i j)) → (∀ i j, 𝓠 (D' i j)) → ∀ v : X₄ℂ,
    𝓠 fun m => sumForm (fun i j => D i j m) (fun i j => D' i j m) v

section Engine

variable (𝓠 : (X₄ℂ → ℂ) → Prop) {s : Set X₄ℂ}

private theorem AgreesWith.contDiffOn (hs : IsOpen s) (hclosed : SumFormClosed 𝓠 s) {f : X₄ℂ → ℂ}
    (hf : AgreesWith 𝓠 s f) : ContDiffOn ℝ (⊤ : ℕ∞) f s := by
  obtain ⟨q, hq, hfq⟩ := hf
  exact (contDiffOn_of_sumForm_closed 𝓠 hs hclosed q hq).congr hfq

private theorem AgreesWith.fderiv_apply (hs : IsOpen s) (hclosed : SumFormClosed 𝓠 s) (hcomb : CombClosed 𝓠)
    {f : X₄ℂ → ℂ} (hf : AgreesWith 𝓠 s f) (v : X₄ℂ) : AgreesWith 𝓠 s fun m => fderiv ℝ f m v := by
  obtain ⟨q, hq, hfq⟩ := hf
  obtain ⟨D, D', hD, hD', hqD⟩ := hclosed q hq
  refine ⟨_, hcomb D D' hD hD' v, fun m hm => ?_⟩
  have hEq : f =ᶠ[nhds m] q := Filter.eventuallyEq_of_mem (hs.mem_nhds hm) hfq
  show fderiv ℝ f m v = sumForm (fun i j => D i j m) (fun i j => D' i j m) v
  rw [hEq.fderiv_eq, (hqD m hm).fderiv]

private theorem
    AgreesWith.iteratedFDerivWithin_bound (hs : IsOpen s) (hclosed : SumFormClosed 𝓠 s) (hcomb : CombClosed 𝓠)
    {ι : Type} (pt : ι → X₄ℂ) (hpt : ∀ i, pt i ∈ s) (φ : ℕ → ι → ℝ) (hφ0 : ∀ n i, 0 ≤ φ n i) (hφ : Monotone φ)
    (hbound : ∀ q, 𝓠 q → ∃ (C : ℝ) (n : ℕ), ∀ i, ‖q (pt i)‖ ≤ C * φ n i) (j : ℕ) {f : X₄ℂ → ℂ}
    (hf : AgreesWith 𝓠 s f) : ∃ (C : ℝ) (n : ℕ), ∀ i, ‖iteratedFDerivWithin ℝ j f s (pt i)‖ ≤ C * φ n i :=
  DerivEngine.iteratedFDerivWithin_bound_of_closed (Module.finBasis ℝ X₄ℂ) s hs pt hpt φ hφ0 hφ (AgreesWith 𝓠 s)
    (fun _ hg => hg.contDiffOn 𝓠 hs hclosed) (fun _ hg _ => hg.fderiv_apply 𝓠 hs hclosed hcomb _)
    (fun _ hg => by
      obtain ⟨q, hq, hgq⟩ := hg
      obtain ⟨C, n, hC⟩ := hbound q hq
      exact ⟨C, n, fun i => by rw [hgq (hpt i)]; exact hC i⟩)
    j f hf

private theorem AgreesWith.decay_top (hs : IsOpen s) (hclosed : SumFormClosed 𝓠 s) (hcomb : CombClosed 𝓠)
    {ι : Type} (pt : ι → X₄ℂ) (hpt : ∀ i, pt i ∈ s) (rof : ι → ℝ) (hr0 : ∀ i, 0 ≤ rof i)
    (hbound : ∀ q, 𝓠 q → ∀ N : ℕ, ∃ C : ℝ, ∀ i, ‖q (pt i)‖ ≤ C * rof i ^ (-(N : ℝ))) (j N : ℕ) {f : X₄ℂ → ℂ}
    (hf : AgreesWith 𝓠 s f) : ∃ C : ℝ, ∀ i, ‖iteratedFDerivWithin ℝ j f s (pt i)‖ ≤ C * rof i ^ (-(N : ℝ)) := by
  obtain ⟨C, -, hC⟩ := hf.iteratedFDerivWithin_bound 𝓠 hs hclosed hcomb pt hpt (fun _ i => rof i ^ (-(N : ℝ)))
    (fun _ i => Real.rpow_nonneg (hr0 i) _) (fun _ _ _ => le_rfl)
    (fun q hq => by
      obtain ⟨C, hC⟩ := hbound q hq N
      exact ⟨C, 0, hC⟩) j
  exact ⟨C, hC⟩

private theorem AgreesWith.decay_zero (hs : IsOpen s) (hclosed : SumFormClosed 𝓠 s) (hcomb : CombClosed 𝓠)
    {ι : Type} (pt : ι → X₄ℂ) (hpt : ∀ i, pt i ∈ s) (rof : ι → ℝ) (hr0 : ∀ i, 0 < rof i) (hr1 : ∀ i, rof i ≤ 1)
    (hbound : ∀ q, 𝓠 q → ∃ (C : ℝ) (n : ℕ), ∀ i, ‖q (pt i)‖ ≤ C * rof i ^ (-(n : ℝ))) (j : ℕ) {f : X₄ℂ → ℂ}
    (hf : AgreesWith 𝓠 s f) :
    ∃ (C : ℝ) (n : ℕ), ∀ i, ‖iteratedFDerivWithin ℝ j f s (pt i)‖ ≤ C * rof i ^ (-(n : ℝ)) :=
  hf.iteratedFDerivWithin_bound 𝓠 hs hclosed hcomb pt hpt (fun n i => rof i ^ (-(n : ℝ)))
    (fun _ i => Real.rpow_nonneg (hr0 i).le _)
    (by
      intro n n' hnn' i
      exact Real.rpow_le_rpow_of_exponent_ge (hr0 i) (hr1 i) (neg_le_neg (by exact_mod_cast hnn')))
    hbound j

end Engine

private def detNormPow (β : ℂ) (m : X₄ℂ) : ℂ := ((‖detC m‖ ^ 2 : ℝ) : ℂ) ^ β

private theorem detC_mul_conj (m : X₄ℂ) : detC m * conj (detC m) = ((‖detC m‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

private theorem isEntryPoly_detC_mul_conj : IsEntryPoly fun m : X₄ℂ => detC m * conj (detC m) :=
  IsEntryPoly.detCoords.mul IsEntryPoly.detCoords.conj_mem

private theorem hasFDerivAt_detNormPow :
    ∃ Db Db' : Fin 2 → Fin 2 → X₄ℂ → ℂ, (∀ i j, IsEntryPoly (Db i j)) ∧ (∀ i j, IsEntryPoly (Db' i j)) ∧
      ∀ (β : ℂ) (m : X₄ℂ), detC m ≠ 0 →
        HasFDerivAt (fun m => detNormPow β m)
          ((β * detNormPow (β - 1) m) • sumForm (fun i j => Db i j m) fun i j => Db' i j m) m := by
  obtain ⟨Db, Db', hDb, hDb', hb'⟩ := isEntryPoly_detC_mul_conj.hasFDerivAt
  refine ⟨Db, Db', hDb, hDb', fun β m hm => ?_⟩
  simp only [detNormPow]
  by_cases hβ : β = 0
  · subst hβ
    have e : (fun m : X₄ℂ => ((‖detC m‖ ^ 2 : ℝ) : ℂ) ^ (0 : ℂ)) = fun _ => (1 : ℂ) := by
      funext m'
      simp
    rw [e]
    refine (hasFDerivAt_const (1 : ℂ) m).congr_fderiv ?_
    refine ContinuousLinearMap.ext fun v => ?_
    simp
  have hpos : 0 < ‖detC m‖ ^ 2 := pow_pos (norm_pos_iff.mpr hm) 2

  have hre : HasFDerivAt (fun m : X₄ℂ => (detC m * conj (detC m)).re)
      (Complex.reCLM.comp (sumForm (fun i j => Db i j m) fun i j => Db' i j m)) m :=
    Complex.reCLM.hasFDerivAt.comp m (hb' m)
  have eN : (fun m : X₄ℂ => (detC m * conj (detC m)).re) = fun m => ‖detC m‖ ^ 2 := by
    funext m'
    rw [detC_mul_conj, Complex.ofReal_re]
  rw [eN] at hre
  obtain ⟨L, hL⟩ : ∃ L : X₄ℂ →L[ℝ] ℝ, HasFDerivAt (fun m : X₄ℂ => ‖detC m‖ ^ 2) L m := ⟨_, hre⟩

  have hofReal : HasFDerivAt (fun m : X₄ℂ => ((‖detC m‖ ^ 2 : ℝ) : ℂ)) (Complex.ofRealCLM.comp L) m :=
    Complex.ofRealCLM.hasFDerivAt.comp m hL
  have eC : (fun m : X₄ℂ => ((‖detC m‖ ^ 2 : ℝ) : ℂ)) = fun m => detC m * conj (detC m) := by
    funext m'
    rw [detC_mul_conj]
  rw [eC] at hofReal
  have hEq : (sumForm (fun i j => Db i j m) fun i j => Db' i j m) = Complex.ofRealCLM.comp L :=
    (hb' m).unique hofReal
  have hcp : HasDerivAt (fun y : ℝ => (y : ℂ) ^ β) (β * ((‖detC m‖ ^ 2 : ℝ) : ℂ) ^ (β - 1)) (‖detC m‖ ^ 2) :=
    hasDerivAt_ofReal_cpow_const hpos.ne' hβ
  have hcomp := hcp.hasFDerivAt.comp m hL
  refine HasFDerivAt.congr_fderiv (hcomp : HasFDerivAt (fun m : X₄ℂ => ((‖detC m‖ ^ 2 : ℝ) : ℂ) ^ β) _ m) ?_
  rw [hEq]
  refine ContinuousLinearMap.ext fun v => ?_
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
    Complex.real_smul,
    ContinuousLinearMap.smul_apply, Complex.ofRealCLM_apply, smul_eq_mul]
  ring

private inductive InClsC (F : Freq) (χ : ℂ → ℂ) : (X₄ℂ → ℂ) → Prop
  | term {E : X₄ℂ → ℂ} (hE : IsEntryPoly E) (β : ℂ) {Q : X₄ℂ → ℂ → ℂ → ℂ} (hQ : IsPoly Q) :
      InClsC F χ fun m => E m * detNormPow β m * tIntC F Q χ m
  | add {f g : X₄ℂ → ℂ} (hf : InClsC F χ f) (hg : InClsC F χ g) : InClsC F χ fun m => f m + g m
  | smul (c : ℂ) {f : X₄ℂ → ℂ} (hf : InClsC F χ f) : InClsC F χ fun m => c * f m

namespace InClsC

variable {F : Freq} {χ : ℂ → ℂ}

private theorem congr {f g : X₄ℂ → ℂ} (h : InClsC F χ f) (e : f = g) : InClsC F χ g := e ▸ h

private theorem combClosed : CombClosed (InClsC F χ) := by
  intro D D' hD hD' v
  refine ((((smul (v 0 0) (hD 0 0)).add (smul (conj (v 0 0)) (hD' 0 0))).add
      ((smul (v 0 1) (hD 0 1)).add (smul (conj (v 0 1)) (hD' 0 1)))).add
    (((smul (v 1 0) (hD 1 0)).add (smul (conj (v 1 0)) (hD' 1 0))).add
      ((smul (v 1 1) (hD 1 1)).add (smul (conj (v 1 1)) (hD' 1 1))))).congr ?_
  funext m
  simp only [sumForm_apply, Fin.sum_univ_two]
  ring

private theorem sumFormClosed (hχ : Measurable χ) {A : ℕ} (hχA : ∀ t : ℂ, t ≠ 0 → ‖χ t‖ ≤ ‖t‖ ^ A + ‖t‖⁻¹ ^ A)
    {s : Set X₄ℂ} (hdet : ∀ m ∈ s, detC m ≠ 0) : SumFormClosed (InClsC F χ) s := by
  obtain ⟨Db, Db', hDb, hDb', hdpow⟩ := hasFDerivAt_detNormPow
  intro q hq
  induction hq with
  | @term E hE β Q hQ =>
    obtain ⟨DE, DE', hDE, hDE', hE'⟩ := hE.hasFDerivAt
    obtain ⟨DQ, DQ', hDQ, hDQ', hQ'⟩ := hQ.hasFDerivAt_tIntC F hχ hχA
    refine ⟨fun i j m => E m * detNormPow β m * tIntC F (DQ i j) χ m +
        β * (E m * Db i j m) * detNormPow (β - 1) m * tIntC F Q χ m + DE i j m * detNormPow β m * tIntC F Q χ m,
      fun i j m => E m * detNormPow β m * tIntC F (DQ' i j) χ m +
        β * (E m * Db' i j m) * detNormPow (β - 1) m * tIntC F Q χ m + DE' i j m * detNormPow β m * tIntC F Q χ m,
      fun i j => ((term hE β (hDQ i j)).add (term ((hE.mul (hDb i j)).smul β) (β - 1) hQ)).add (term (hDE i j) β hQ),
      fun i j => ((term hE β (hDQ' i j)).add (term ((hE.mul (hDb' i j)).smul β) (β - 1) hQ)).add
        (term (hDE' i j) β hQ),
      fun m hm => ?_⟩
    refine (((hE' m).mul (hdpow β m (hdet m hm))).mul (hQ' m (hdet m hm))).congr_fderiv ?_
    refine ContinuousLinearMap.ext fun v => ?_
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, sumForm_apply, Fin.sum_univ_two,
      smul_eq_mul, Pi.mul_apply]
    ring
  | add _ _ ihf ihg =>
    obtain ⟨Df, Df', hDf, hDf', hf'⟩ := ihf
    obtain ⟨Dg, Dg', hDg, hDg', hg'⟩ := ihg
    refine ⟨fun i j m => Df i j m + Dg i j m, fun i j m => Df' i j m + Dg' i j m, fun i j => (hDf i j).add (hDg i j),
      fun i j => (hDf' i j).add (hDg' i j), fun m hm => ?_⟩
    refine ((hf' m hm).add (hg' m hm)).congr_fderiv ?_
    refine ContinuousLinearMap.ext fun v => ?_
    simp only [ContinuousLinearMap.add_apply, sumForm_apply, Fin.sum_univ_two]
    ring
  | smul c _ ih =>
    obtain ⟨Df, Df', hDf, hDf', hf'⟩ := ih
    refine ⟨fun i j m => c * Df i j m, fun i j m => c * Df' i j m, fun i j => smul c (hDf i j),
      fun i j => smul c (hDf' i j), fun m hm => ?_⟩
    refine ((hf' m hm).const_mul c).congr_fderiv ?_
    exact smul_sumForm c _ _

private theorem
    contDiffOn_of_agreesWith (hχ : Measurable χ) {A : ℕ} (hχA : ∀ t : ℂ, t ≠ 0 → ‖χ t‖ ≤ ‖t‖ ^ A + ‖t‖⁻¹ ^ A)
    {s : Set X₄ℂ} (hs : IsOpen s) (hdet : ∀ m ∈ s, detC m ≠ 0) {f : X₄ℂ → ℂ} (hf : AgreesWith (InClsC F χ) s f) :
    ContDiffOn ℝ (⊤ : ℕ∞) f s :=
  hf.contDiffOn (InClsC F χ) hs (sumFormClosed hχ hχA hdet)

end InClsC

private structure IsGatePt (ρ : ℝ) (m : X₄ℂ) : Prop extends IsGateC ρ m where
  rho_pos : 0 < ρ
  norm_det : ‖detC m‖ = ρ

namespace IsGatePt

variable {ρ : ℝ} {m : X₄ℂ}

private theorem entries_le_rho (h : IsGatePt ρ m) (hρ : 1 ≤ ρ) (i j : Fin 2) : ‖m i j‖ ≤ ρ := by
  fin_cases i
  · simpa using h.top j
  · simpa using (h.bot j).trans hρ

private theorem entries_le_one (h : IsGatePt ρ m) (hρ : ρ ≤ 1) (i j : Fin 2) : ‖m i j‖ ≤ 1 := by
  fin_cases i
  · simpa using (h.top j).trans hρ
  · simpa using h.bot j

private theorem norm_detNormPow (h : IsGatePt ρ m) (β : ℂ) : ‖detNormPow β m‖ = (ρ ^ 2) ^ β.re := by
  have hpos : 0 < ‖detC m‖ ^ 2 := pow_pos (norm_pos_iff.mpr h.detC_ne) 2
  rw [detNormPow, Complex.norm_cpow_eq_rpow_re_of_pos hpos, h.norm_det]

end IsGatePt

private theorem inv_pow_eq_rpow_neg {r : ℝ} (hr : 0 ≤ r) (n : ℕ) : r⁻¹ ^ n = r ^ (-(n : ℝ)) := by
  rw [Real.rpow_neg hr, Real.rpow_natCast, inv_pow]

private theorem rpow_le_of_one_le {r : ℝ} (hr : 1 ≤ r) (x : ℝ) : r ^ x ≤ r ^ ⌈x⌉₊ := by
  rw [← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le hr (Nat.le_ceil _)

private theorem rpow_le_of_le_one {r : ℝ} (hr0 : 0 < r) (hr : r ≤ 1) (x : ℝ) : r ^ x ≤ r⁻¹ ^ ⌈-x⌉₊ := by
  rw [inv_pow_eq_rpow_neg hr0.le]
  exact Real.rpow_le_rpow_of_exponent_ge hr0 hr (by linarith [Nat.le_ceil (-x)])

private theorem one_add_pow_le {S : ℝ} (hS : 0 ≤ S) (k : ℕ) : (1 + S) ^ k ≤ 2 ^ k * (1 + S ^ k) := by
  rcases le_total S 1 with hs | hs
  · calc (1 + S) ^ k ≤ 2 ^ k := pow_le_pow_left₀ (by positivity) (by linarith) k
      _ ≤ 2 ^ k * (1 + S ^ k) := le_mul_of_one_le_right (by positivity) (by linarith [pow_nonneg hS k])
  · calc (1 + S) ^ k ≤ (2 * S) ^ k := pow_le_pow_left₀ (by positivity) (by linarith) k
      _ = 2 ^ k * S ^ k := mul_pow 2 S k
      _ ≤ 2 ^ k * (1 + S ^ k) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)

private theorem two_pow_mul_le {S : ℝ} (hS : 0 ≤ S) {a b : ℕ} (hab : a ≤ b) (d : ℕ) :
    (S ^ b + S ^ a) * (1 + S) ^ d ≤ 2 * 2 ^ (b + d) * (1 + S ^ (b + d)) := by
  have h1 : 1 ≤ 1 + S := by linarith
  have hb' : S ^ b ≤ (1 + S) ^ b := pow_le_pow_left₀ hS (by linarith) b
  have ha' : S ^ a ≤ (1 + S) ^ b := (pow_le_pow_left₀ hS (by linarith) a).trans (pow_le_pow_right₀ h1 hab)
  have hd : 0 ≤ (1 + S) ^ d := by positivity
  calc (S ^ b + S ^ a) * (1 + S) ^ d ≤ 2 * (1 + S) ^ b * (1 + S) ^ d :=
        mul_le_mul_of_nonneg_right (by linarith) hd
    _ = 2 * (1 + S) ^ (b + d) := by ring
    _ ≤ 2 * (2 ^ (b + d) * (1 + S ^ (b + d))) := mul_le_mul_of_nonneg_left (one_add_pow_le hS _) (by norm_num)
    _ = 2 * 2 ^ (b + d) * (1 + S ^ (b + d)) := by ring

private theorem norm_pow_eq_scale {ρ : ℝ} (hρ : ρ ≠ 0) (t : ℂ) (j : ℕ) : ‖t‖ ^ j = ρ⁻¹ ^ j * (ρ * ‖t‖) ^ j := by
  rw [← mul_pow, ← mul_assoc, inv_mul_cancel₀ hρ, one_mul]

private theorem weight_mul_general {r : ℝ} (hr : r ≠ 0) (A L : ℕ) :
    (r ^ A + r⁻¹ ^ A) * (r ^ (A + 2 + L) * r⁻¹ ^ 2) = r ^ (2 * A + L) + r ^ L := by
  have h1 : r ^ (A + 2 + L) * r⁻¹ ^ 2 = r ^ (A + L) := by
    rw [show A + 2 + L = A + L + 2 by ring, pow_add, mul_assoc, ← mul_pow, mul_inv_cancel₀ hr, one_pow, mul_one]
  have h2 : r⁻¹ ^ A * r ^ A = 1 := by rw [← mul_pow, inv_mul_cancel₀ hr, one_pow]
  have h3 : r⁻¹ ^ A * r ^ (A + L) = r ^ L := by rw [pow_add, ← mul_assoc, h2, one_mul]
  rw [h1, add_mul, h3]
  ring

private def gateDomC (k : ℕ) (s : ℂ) : ℝ := 2 * 2 ^ k * ((1 + ‖s‖ ^ k) * Real.exp (-(2 * Real.pi / 2) * ‖s‖ ^ 2))

private theorem gateDomC_nonneg (k : ℕ) (s : ℂ) : 0 ≤ gateDomC k s := by
  unfold gateDomC
  positivity

open MeasureTheory in
private theorem integrable_gateDomC (k : ℕ) : Integrable (gateDomC k) :=
  (integrable_one_add_norm_pow_mul_exp (by positivity : (0 : ℝ) < 2 * Real.pi / 2) k).const_mul _

namespace IsPoly

open MeasureTheory in

private theorem tIntC_gate_core (F : Freq) {Q : X₄ℂ → ℂ → ℂ → ℂ} (hQ : IsPoly Q) {χ : ℂ → ℂ} {A : ℕ}
    (hχA : ∀ t : ℂ, t ≠ 0 → ‖χ t‖ ≤ ‖t‖ ^ A + ‖t‖⁻¹ ^ A) (L : ℕ) :
    ∃ (K : ℝ) (d : ℕ), 0 ≤ K ∧ ∀ (ρ : ℝ) (m : X₄ℂ), IsGatePt ρ m → ∀ (b : ℝ) (e : ℕ), 0 ≤ b →
      (∀ t : ℂ, 1 + ‖t‖ ≤ b * (1 + ρ * ‖t‖)) → ρ⁻¹ ^ (2 * A + L) ≤ ρ⁻¹ ^ e → ρ⁻¹ ^ L ≤ ρ⁻¹ ^ e →
      ‖tIntC F Q χ m‖ ≤ K * b ^ d * ρ⁻¹ ^ (e + 2) := by
  obtain ⟨C, d, hC, hCb⟩ := hQ.innFC_gate_bound F (A + 2 + L)
  have hM0 : 0 ≤ ∫ s : ℂ, gateDomC (2 * A + L + d) s := integral_nonneg (gateDomC_nonneg _)
  refine ⟨C * ∫ s : ℂ, gateDomC (2 * A + L + d) s, d, mul_nonneg hC hM0, fun ρ m hg b e hb hb1 h1 h2 => ?_⟩
  have hρ : 0 < ρ := hg.rho_pos
  have hdom : Integrable fun t : ℂ => C * ρ⁻¹ ^ e * b ^ d * gateDomC (2 * A + L + d) (ρ • t) :=
    ((integrable_gateDomC _).comp_smul hρ.ne').const_mul _
  have hpt : ∀ᵐ t : ℂ, ‖χ t * innFC F Q m t‖ ≤ C * ρ⁻¹ ^ e * b ^ d * gateDomC (2 * A + L + d) (ρ • t) := by
    refine ae_ne_zero_C.mono fun t ht => ?_
    have hr : ‖t‖ ≠ 0 := norm_ne_zero_iff.mpr ht
    have hw := hχA t ht
    have hi := hCb ρ m hg.toIsGateC t
    have hs : ‖ρ • t‖ = ρ * ‖t‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
    have hEpos : 0 < Real.exp (-(2 * Real.pi / 2) * (ρ * ‖t‖) ^ 2) := Real.exp_pos _
    have hpow1 : ‖t‖ ^ (2 * A + L) ≤ ρ⁻¹ ^ e * (ρ * ‖t‖) ^ (2 * A + L) := by
      rw [norm_pow_eq_scale hρ.ne' t (2 * A + L)]
      exact mul_le_mul_of_nonneg_right h1 (by positivity)
    have hpow2 : ‖t‖ ^ L ≤ ρ⁻¹ ^ e * (ρ * ‖t‖) ^ L := by
      rw [norm_pow_eq_scale hρ.ne' t L]
      exact mul_le_mul_of_nonneg_right h2 (by positivity)
    have hone : (1 + ‖t‖) ^ d ≤ b ^ d * (1 + ρ * ‖t‖) ^ d := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) (hb1 t) d
    have hprof : ((ρ * ‖t‖) ^ (2 * A + L) + (ρ * ‖t‖) ^ L) * (1 + ρ * ‖t‖) ^ d *
        Real.exp (-(2 * Real.pi / 2) * (ρ * ‖t‖) ^ 2) ≤ gateDomC (2 * A + L + d) (ρ • t) := by
      unfold gateDomC
      rw [hs]
      calc ((ρ * ‖t‖) ^ (2 * A + L) + (ρ * ‖t‖) ^ L) * (1 + ρ * ‖t‖) ^ d *
            Real.exp (-(2 * Real.pi / 2) * (ρ * ‖t‖) ^ 2)
          ≤ 2 * 2 ^ (2 * A + L + d) * (1 + (ρ * ‖t‖) ^ (2 * A + L + d)) *
              Real.exp (-(2 * Real.pi / 2) * (ρ * ‖t‖) ^ 2) :=
            mul_le_mul_of_nonneg_right (two_pow_mul_le (by positivity) (by omega) d) hEpos.le
        _ = 2 * 2 ^ (2 * A + L + d) *
              ((1 + (ρ * ‖t‖) ^ (2 * A + L + d)) * Real.exp (-(2 * Real.pi / 2) * (ρ * ‖t‖) ^ 2)) := by ring
    calc ‖χ t * innFC F Q m t‖ = ‖χ t‖ * ‖innFC F Q m t‖ := norm_mul _ _
      _ ≤ (‖t‖ ^ A + ‖t‖⁻¹ ^ A) *
            (C * (‖t‖ ^ (A + 2 + L) * ‖t‖⁻¹ ^ 2) * ((1 + ‖t‖) ^ d * Real.exp (-(2 * Real.pi / 2) * (ρ * ‖t‖) ^ 2))) :=
          mul_le_mul hw hi (norm_nonneg _) (by positivity)
      _ = C * ((‖t‖ ^ (2 * A + L) + ‖t‖ ^ L) * (1 + ‖t‖) ^ d * Real.exp (-(2 * Real.pi / 2) * (ρ * ‖t‖) ^ 2)) := by
          rw [← weight_mul_general hr A L]
          ring
      _ ≤ C * ((ρ⁻¹ ^ e * (ρ * ‖t‖) ^ (2 * A + L) + ρ⁻¹ ^ e * (ρ * ‖t‖) ^ L) * (b ^ d * (1 + ρ * ‖t‖) ^ d) *
            Real.exp (-(2 * Real.pi / 2) * (ρ * ‖t‖) ^ 2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
            (mul_le_mul (add_le_add hpow1 hpow2) hone (by positivity) (by positivity)) hEpos.le) hC
      _ = C * ρ⁻¹ ^ e * b ^ d * (((ρ * ‖t‖) ^ (2 * A + L) + (ρ * ‖t‖) ^ L) * (1 + ρ * ‖t‖) ^ d *
            Real.exp (-(2 * Real.pi / 2) * (ρ * ‖t‖) ^ 2)) := by
          ring
      _ ≤ C * ρ⁻¹ ^ e * b ^ d * gateDomC (2 * A + L + d) (ρ • t) := mul_le_mul_of_nonneg_left hprof (by positivity)
  have hsc := Measure.integral_comp_smul (μ := volume) (gateDomC (2 * A + L + d)) ρ
  have habs : |(ρ ^ 2)⁻¹| = ρ⁻¹ ^ 2 := by
    rw [abs_inv, abs_pow, abs_of_pos hρ, inv_pow]
  rw [Complex.finrank_real_complex, habs, smul_eq_mul] at hsc
  show ‖∫ t : ℂ, χ t * innFC F Q m t‖ ≤ _
  calc ‖∫ t : ℂ, χ t * innFC F Q m t‖ ≤ ∫ t : ℂ, C * ρ⁻¹ ^ e * b ^ d * gateDomC (2 * A + L + d) (ρ • t) :=
        norm_integral_le_of_norm_le hdom hpt
    _ = C * (∫ s : ℂ, gateDomC (2 * A + L + d) s) * b ^ d * ρ⁻¹ ^ (e + 2) := by
        rw [integral_const_mul, hsc]
        ring

end IsPoly

namespace InClsC

variable {F : Freq} {χ : ℂ → ℂ}

private theorem gate_bound_top {A : ℕ} (hχA : ∀ t : ℂ, t ≠ 0 → ‖χ t‖ ≤ ‖t‖ ^ A + ‖t‖⁻¹ ^ A) {q : X₄ℂ → ℂ}
    (hq : InClsC F χ q) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ρ : ℝ) (m : X₄ℂ), IsGatePt ρ m → 1 ≤ ρ → ‖q m‖ ≤ C * ρ⁻¹ ^ N := by
  induction hq with
  | @term E hE β Q hQ =>
    obtain ⟨CE, dE, hCE, hEb⟩ := hE.norm_le_of_entries_le
    obtain ⟨K, d, hK, hKb⟩ := hQ.tIntC_gate_core F hχA (N + dE + 2 * ⌈β.re⌉₊)
    refine ⟨CE * K, by positivity, fun ρ m hg hρ => ?_⟩
    have hρ0 : 0 < ρ := hg.rho_pos
    have hyi : ρ⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hρ
    have h1 : ‖E m‖ ≤ CE * ρ ^ dE := hEb m ρ hρ (hg.entries_le_rho hρ)
    have h2 : ‖detNormPow β m‖ ≤ (ρ ^ 2) ^ ⌈β.re⌉₊ := by
      rw [hg.norm_detNormPow]
      exact rpow_le_of_one_le (one_le_pow₀ hρ) β.re
    have hb1 : ∀ t : ℂ, 1 + ‖t‖ ≤ 1 * (1 + ρ * ‖t‖) := fun t => by
      rw [one_mul]
      exact add_le_add le_rfl (le_mul_of_one_le_left (norm_nonneg t) hρ)
    have h3 := hKb ρ m hg 1 (N + dE + 2 * ⌈β.re⌉₊) zero_le_one hb1
      (pow_le_pow_of_le_one (by positivity) hyi (by omega)) le_rfl
    rw [one_pow, mul_one] at h3
    have hw0 : 0 ≤ ρ⁻¹ := inv_nonneg.2 hρ0.le
    have hw : ρ * ρ⁻¹ = 1 := mul_inv_cancel₀ hρ0.ne'
    show ‖E m * detNormPow β m * tIntC F Q χ m‖ ≤ CE * K * ρ⁻¹ ^ N
    revert hyi h3 hw0 hw
    generalize ρ⁻¹ = w
    intro hyi h3 hw0 hw
    have hcancel : ρ ^ dE * (ρ ^ 2) ^ ⌈β.re⌉₊ * w ^ (N + dE + 2 * ⌈β.re⌉₊ + 2) = w ^ (N + 2) := by
      rw [show ρ ^ dE * (ρ ^ 2) ^ ⌈β.re⌉₊ * w ^ (N + dE + 2 * ⌈β.re⌉₊ + 2) =
        (ρ * w) ^ (dE + 2 * ⌈β.re⌉₊) * w ^ (N + 2) by ring, hw, one_pow, one_mul]
    calc ‖E m * detNormPow β m * tIntC F Q χ m‖ = ‖E m‖ * ‖detNormPow β m‖ * ‖tIntC F Q χ m‖ := by
          rw [norm_mul, norm_mul]
      _ ≤ CE * ρ ^ dE * (ρ ^ 2) ^ ⌈β.re⌉₊ * (K * w ^ (N + dE + 2 * ⌈β.re⌉₊ + 2)) :=
          mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) (by positivity)) h3 (norm_nonneg _) (by positivity)
      _ = CE * K * (ρ ^ dE * (ρ ^ 2) ^ ⌈β.re⌉₊ * w ^ (N + dE + 2 * ⌈β.re⌉₊ + 2)) := by ring
      _ = CE * K * w ^ (N + 2) := by rw [hcancel]
      _ ≤ CE * K * w ^ N :=
          mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hw0 hyi (by omega)) (by positivity)
  | @add f g _ _ ihf ihg =>
    obtain ⟨C₁, hC₁, h₁⟩ := ihf
    obtain ⟨C₂, hC₂, h₂⟩ := ihg
    refine ⟨C₁ + C₂, by positivity, fun ρ m hg hρ => ?_⟩
    show ‖f m + g m‖ ≤ (C₁ + C₂) * ρ⁻¹ ^ N
    rw [add_mul]
    exact (norm_add_le _ _).trans (add_le_add (h₁ ρ m hg hρ) (h₂ ρ m hg hρ))
  | @smul c f _ ih =>
    obtain ⟨C, hC, h⟩ := ih
    refine ⟨‖c‖ * C, by positivity, fun ρ m hg hρ => ?_⟩
    show ‖c * f m‖ ≤ ‖c‖ * C * ρ⁻¹ ^ N
    rw [norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (h ρ m hg hρ) (norm_nonneg c)

private theorem gate_bound_zero {A : ℕ} (hχA : ∀ t : ℂ, t ≠ 0 → ‖χ t‖ ≤ ‖t‖ ^ A + ‖t‖⁻¹ ^ A) {q : X₄ℂ → ℂ}
    (hq : InClsC F χ q) :
    ∃ (C : ℝ) (n : ℕ), 0 ≤ C ∧ ∀ (ρ : ℝ) (m : X₄ℂ), IsGatePt ρ m → ρ ≤ 1 → ‖q m‖ ≤ C * ρ⁻¹ ^ n := by
  induction hq with
  | @term E hE β Q hQ =>
    obtain ⟨CE, dE, hCE, hEb⟩ := hE.norm_le_of_entries_le
    obtain ⟨K, d, hK, hKb⟩ := hQ.tIntC_gate_core F hχA 0
    refine ⟨CE * K, 2 * ⌈-β.re⌉₊ + (d + (2 * A + 0 + 2)), by positivity, fun ρ m hg hρ => ?_⟩
    have hρ0 : 0 < ρ := hg.rho_pos
    have hyi : 1 ≤ ρ⁻¹ := (one_le_inv₀ hρ0).2 hρ
    have h1 : ‖E m‖ ≤ CE := by
      have h := hEb m 1 le_rfl (hg.entries_le_one hρ)
      rwa [one_pow, mul_one] at h
    have h2 : ‖detNormPow β m‖ ≤ (ρ⁻¹ ^ 2) ^ ⌈-β.re⌉₊ := by
      rw [hg.norm_detNormPow, inv_pow]
      exact rpow_le_of_le_one (by positivity) (pow_le_one₀ hρ0.le hρ) β.re
    have hb1 : ∀ t : ℂ, 1 + ‖t‖ ≤ ρ⁻¹ * (1 + ρ * ‖t‖) := fun t => by
      have e : ρ⁻¹ * (1 + ρ * ‖t‖) = ρ⁻¹ + ‖t‖ := by
        rw [mul_add, ← mul_assoc, inv_mul_cancel₀ hρ0.ne', mul_one, one_mul]
      rw [e]
      exact add_le_add hyi le_rfl
    have h3 := hKb ρ m hg ρ⁻¹ (2 * A + 0) (inv_nonneg.2 hρ0.le) hb1 le_rfl (pow_le_pow_right₀ hyi (Nat.zero_le _))
    have hw0 : 0 ≤ ρ⁻¹ := inv_nonneg.2 hρ0.le
    show ‖E m * detNormPow β m * tIntC F Q χ m‖ ≤ CE * K * ρ⁻¹ ^ (2 * ⌈-β.re⌉₊ + (d + (2 * A + 0 + 2)))
    revert h2 h3 hw0
    generalize ρ⁻¹ = w
    intro h2 h3 hw0
    calc ‖E m * detNormPow β m * tIntC F Q χ m‖ = ‖E m‖ * ‖detNormPow β m‖ * ‖tIntC F Q χ m‖ := by
          rw [norm_mul, norm_mul]
      _ ≤ CE * (w ^ 2) ^ ⌈-β.re⌉₊ * (K * w ^ d * w ^ (2 * A + 0 + 2)) :=
          mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) hCE) h3 (norm_nonneg _) (mul_nonneg hCE (by positivity))
      _ = CE * K * w ^ (2 * ⌈-β.re⌉₊ + (d + (2 * A + 0 + 2))) := by ring
  | @add f g _ _ ihf ihg =>
    obtain ⟨C₁, n₁, hC₁, h₁⟩ := ihf
    obtain ⟨C₂, n₂, hC₂, h₂⟩ := ihg
    refine ⟨C₁ + C₂, max n₁ n₂, by positivity, fun ρ m hg hρ => ?_⟩
    have hyi : 1 ≤ ρ⁻¹ := (one_le_inv₀ hg.rho_pos).2 hρ
    show ‖f m + g m‖ ≤ (C₁ + C₂) * ρ⁻¹ ^ max n₁ n₂
    calc ‖f m + g m‖ ≤ ‖f m‖ + ‖g m‖ := norm_add_le _ _
      _ ≤ C₁ * ρ⁻¹ ^ n₁ + C₂ * ρ⁻¹ ^ n₂ := add_le_add (h₁ ρ m hg hρ) (h₂ ρ m hg hρ)
      _ ≤ C₁ * ρ⁻¹ ^ max n₁ n₂ + C₂ * ρ⁻¹ ^ max n₁ n₂ :=
          add_le_add (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hyi (le_max_left _ _)) hC₁)
            (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hyi (le_max_right _ _)) hC₂)
      _ = (C₁ + C₂) * ρ⁻¹ ^ max n₁ n₂ := (add_mul _ _ _).symm
  | @smul c f _ ih =>
    obtain ⟨C, n, hC, h⟩ := ih
    refine ⟨‖c‖ * C, n, by positivity, fun ρ m hg hρ => ?_⟩
    show ‖c * f m‖ ≤ ‖c‖ * C * ρ⁻¹ ^ n
    rw [norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (h ρ m hg hρ) (norm_nonneg c)

private theorem
    decay_top_of_agreesWith (hχ : Measurable χ) {A : ℕ} (hχA : ∀ t : ℂ, t ≠ 0 → ‖χ t‖ ≤ ‖t‖ ^ A + ‖t‖⁻¹ ^ A)
    {s : Set X₄ℂ} (hs : IsOpen s) (hdet : ∀ m ∈ s, detC m ≠ 0) {f : X₄ℂ → ℂ} (hf : AgreesWith (InClsC F χ) s f)
    {ι : Type} (pt : ι → X₄ℂ) (rof : ι → ℝ) (hpt : ∀ i, pt i ∈ s) (hgate : ∀ i, IsGatePt (rof i) (pt i))
    (hr : ∀ i, 1 ≤ rof i) (j N : ℕ) :
    ∃ C : ℝ, ∀ i, ‖iteratedFDerivWithin ℝ j f s (pt i)‖ ≤ C * rof i ^ (-(N : ℝ)) := by
  refine hf.decay_top (InClsC F χ) hs (sumFormClosed hχ hχA hdet) combClosed pt hpt rof
    (fun i => (hgate i).rho_pos.le) ?_ j N
  intro q hq N'
  obtain ⟨C, _, hC⟩ := gate_bound_top hχA hq N'
  refine ⟨C, fun i => ?_⟩
  rw [← inv_pow_eq_rpow_neg (hgate i).rho_pos.le]
  exact hC (rof i) (pt i) (hgate i) (hr i)

private theorem
    decay_zero_of_agreesWith (hχ : Measurable χ) {A : ℕ} (hχA : ∀ t : ℂ, t ≠ 0 → ‖χ t‖ ≤ ‖t‖ ^ A + ‖t‖⁻¹ ^ A)
    {s : Set X₄ℂ} (hs : IsOpen s) (hdet : ∀ m ∈ s, detC m ≠ 0) {f : X₄ℂ → ℂ} (hf : AgreesWith (InClsC F χ) s f)
    {ι : Type} (pt : ι → X₄ℂ) (rof : ι → ℝ) (hpt : ∀ i, pt i ∈ s) (hgate : ∀ i, IsGatePt (rof i) (pt i))
    (hr : ∀ i, rof i ≤ 1) (j : ℕ) :
    ∃ (C : ℝ) (n : ℕ), ∀ i, ‖iteratedFDerivWithin ℝ j f s (pt i)‖ ≤ C * rof i ^ (-(n : ℝ)) := by
  refine hf.decay_zero (InClsC F χ) hs (sumFormClosed hχ hχA hdet) combClosed pt hpt rof
    (fun i => (hgate i).rho_pos) hr ?_ j
  intro q hq
  obtain ⟨C, n, _, hC⟩ := gate_bound_zero hχA hq
  refine ⟨C, n, fun i => ?_⟩
  rw [← inv_pow_eq_rpow_neg (hgate i).rho_pos.le]
  exact hC (rof i) (pt i) (hgate i) (hr i)

end InClsC

end ArchEngineC
p2m_reactivate "P2MW.S_LanglandsTunnell_Converse_exists_archDatumC_W_ne_zero.ArchEngineC"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Converse_exists_archDatumC_W_ne_zero.ArchEngineC"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Converse_exists_archDatumC_W_ne_zero.ArchEngineC"

section

open MeasureTheory
open LanglandsTunnell.Converse.ArchC
open LanglandsTunnell.ArchPlace (complexTestFun)
open TateComplex.Datum (PsiC innerWC WmemC)
open scoped ComplexConjugate FourierTransform

noncomputable section

namespace ArchEngineC

local notation "X₄ℂ" => (Fin 2 → Fin 2 → ℂ)

private theorem glSet_eq_detC : glSet = {m : X₄ℂ | detC m ≠ 0} := by
  ext m
  simp only [glSet, Set.mem_setOf_eq, detC_eq_det]

private theorem isOpen_glSet : IsOpen glSet := by
  rw [glSet_eq_detC]
  exact isOpen_ne_fun continuous_detC continuous_const

private theorem detC_ne_of_mem_glSet : ∀ m ∈ glSet, detC m ≠ 0 := fun m hm => by
  rw [detC_eq_det]
  exact hm

private theorem measurable_quasiChar (u : ℂ) (k : ℤ) : Measurable (quasiChar u k) := by
  have hn : Measurable fun z : ℂ => ((‖z‖ : ℝ) : ℂ) := (Complex.continuous_ofReal.comp continuous_norm).measurable
  show Measurable fun z : ℂ => ((‖z‖ : ℝ) : ℂ) ^ (2 * u) * (z / ((‖z‖ : ℝ) : ℂ)) ^ k
  exact (hn.pow_const (2 * u)).mul ((measurable_id.div hn).pow_const k)

private theorem norm_quasiChar (u : ℂ) (k : ℤ) {t : ℂ} (ht : t ≠ 0) : ‖quasiChar u k t‖ = (‖t‖ ^ 2) ^ u.re := by
  have hpos : 0 < ‖t‖ ^ 2 := pow_pos (norm_pos_iff.mpr ht) 2
  have hunit : ‖t / ((‖t‖ : ℝ) : ℂ)‖ = 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm, div_self (norm_ne_zero_iff.mpr ht)]
  rw [TateComplex.Datum.quasiChar_eq_sq_cpow u k ht, norm_mul, norm_zpow, hunit, one_zpow, one_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hpos]

private theorem norm_quasiChar_le (u : ℂ) (k : ℤ) (t : ℂ) (ht : t ≠ 0) :
    ‖quasiChar u k t‖ ≤
      ‖t‖ ^ max (2 * ⌈u.re⌉₊) (2 * ⌈-u.re⌉₊) + ‖t‖⁻¹ ^ max (2 * ⌈u.re⌉₊) (2 * ⌈-u.re⌉₊) := by
  have h0 : 0 < ‖t‖ := norm_pos_iff.mpr ht
  rw [norm_quasiChar u k ht]
  rcases le_total 1 ‖t‖ with h1 | h1
  · calc (‖t‖ ^ 2) ^ u.re ≤ (‖t‖ ^ 2) ^ ⌈u.re⌉₊ := rpow_le_of_one_le (one_le_pow₀ h1) u.re
      _ = ‖t‖ ^ (2 * ⌈u.re⌉₊) := (pow_mul ‖t‖ 2 _).symm
      _ ≤ ‖t‖ ^ max (2 * ⌈u.re⌉₊) (2 * ⌈-u.re⌉₊) := pow_le_pow_right₀ h1 (le_max_left _ _)
      _ ≤ ‖t‖ ^ max (2 * ⌈u.re⌉₊) (2 * ⌈-u.re⌉₊) + ‖t‖⁻¹ ^ max (2 * ⌈u.re⌉₊) (2 * ⌈-u.re⌉₊) :=
          le_add_of_nonneg_right (by positivity)
  · calc (‖t‖ ^ 2) ^ u.re ≤ (‖t‖ ^ 2)⁻¹ ^ ⌈-u.re⌉₊ :=
          rpow_le_of_le_one (by positivity) (pow_le_one₀ h0.le h1) u.re
      _ = ‖t‖⁻¹ ^ (2 * ⌈-u.re⌉₊) := by rw [← inv_pow, ← pow_mul]
      _ ≤ ‖t‖⁻¹ ^ max (2 * ⌈u.re⌉₊) (2 * ⌈-u.re⌉₊) := pow_le_pow_right₀ ((one_le_inv₀ h0).2 h1) (le_max_right _ _)
      _ ≤ ‖t‖ ^ max (2 * ⌈u.re⌉₊) (2 * ⌈-u.re⌉₊) + ‖t‖⁻¹ ^ max (2 * ⌈u.re⌉₊) (2 * ⌈-u.re⌉₊) :=
          le_add_of_nonneg_left (by positivity)

private theorem isK_rows {k : Matrix (Fin 2) (Fin 2) ℂ} (hk : IsK k) :
    k 0 0 * conj (k 0 0) + k 0 1 * conj (k 0 1) = 1 ∧ k 1 0 * conj (k 1 0) + k 1 1 * conj (k 1 1) = 1 ∧
      k 0 0 * conj (k 1 0) + k 0 1 * conj (k 1 1) = 0 ∧ k 1 0 * conj (k 0 0) + k 1 1 * conj (k 0 1) = 0 := by
  have h : k * star k = 1 := Matrix.mem_unitaryGroup_iff.1 hk
  have h00 := congrFun (congrFun h 0) 0
  have h11 := congrFun (congrFun h 1) 1
  have h01 := congrFun (congrFun h 0) 1
  have h10 := congrFun (congrFun h 1) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, Matrix.one_apply_eq,
    Matrix.one_apply_ne (zero_ne_one : (0 : Fin 2) ≠ 1), Matrix.one_apply_ne (one_ne_zero : (1 : Fin 2) ≠ 0)]
    at h00 h11 h01 h10
  exact ⟨h00, h11, h01, h10⟩

private theorem norm_det_of_isK {k : Matrix (Fin 2) (Fin 2) ℂ} (hk : IsK k) : ‖k.det‖ = 1 := by
  have h : star k.det * k.det = 1 := Unitary.star_mul_self_of_mem (Matrix.det_of_mem_unitary hk)
  have h3 : k.det * conj k.det = 1 := by
    rw [mul_comm]
    exact h
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at h3
  have h2 : ‖k.det‖ ^ 2 = 1 := by exact_mod_cast h3
  nlinarith [norm_nonneg k.det, h2]

private theorem
    detC_diagOneMulCoords (z : ℂ) (k : Matrix (Fin 2) (Fin 2) ℂ) : detC (diagOneMulCoords z k) = z * k.det := by
  rw [detC_eq_det, diagOneMulCoords, Equiv.apply_symm_apply, TateComplex.Datum.det_diagOne_mul]

private theorem diagOneMulCoords_entries (z : ℂ) (k : Matrix (Fin 2) (Fin 2) ℂ) :
    diagOneMulCoords z k 0 0 = z * k 0 0 ∧ diagOneMulCoords z k 0 1 = z * k 0 1 ∧
      diagOneMulCoords z k 1 0 = k 1 0 ∧ diagOneMulCoords z k 1 1 = k 1 1 := by
  simp only [diagOneMulCoords, Matrix.of_symm_apply, Matrix.mul_apply, Fin.sum_univ_two]
  simp [diagOne]

private theorem mem_glSet_diagOneMulCoords {z : ℂ} (hz : z ≠ 0) {k : Matrix (Fin 2) (Fin 2) ℂ} (hk : IsK k) :
    diagOneMulCoords z k ∈ glSet := by
  rw [glSet_eq_detC, Set.mem_setOf_eq, detC_diagOneMulCoords]
  exact mul_ne_zero hz (norm_pos_iff.mp (by rw [norm_det_of_isK hk]; exact one_pos))

private theorem isGatePt_diagOneMulCoords {z : ℂ} (hz : z ≠ 0) {k : Matrix (Fin 2) (Fin 2) ℂ} (hk : IsK k) :
    IsGatePt ‖z‖ (diagOneMulCoords z k) := by
  obtain ⟨r0, r1, r01, r10⟩ := isK_rows hk
  obtain ⟨p00, p01, p10, p11⟩ := diagOneMulCoords_entries z k
  have hsq : ∀ a b : ℂ, a * conj a + b * conj b = 1 → ‖a‖ ≤ 1 := fun a b hab => by
    rw [Complex.mul_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at hab
    have hab' : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1 := by exact_mod_cast hab
    nlinarith [norm_nonneg a, norm_nonneg b, sq_nonneg ‖b‖]
  have hk00 : ‖k 0 0‖ ≤ 1 := hsq _ _ r0
  have hk01 : ‖k 0 1‖ ≤ 1 := hsq _ _ (by rw [add_comm]; exact r0)
  have hk10 : ‖k 1 0‖ ≤ 1 := hsq _ _ r1
  have hk11 : ‖k 1 1‖ ≤ 1 := hsq _ _ (by rw [add_comm]; exact r1)
  have hz0 : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hdet : detC (diagOneMulCoords z k) = z * k.det := detC_diagOneMulCoords z k
  have hnorm : ‖detC (diagOneMulCoords z k)‖ = ‖z‖ := by
    rw [hdet, norm_mul, norm_det_of_isK hk, mul_one]
  have hr00 : ‖z * k 0 0‖ ≤ ‖z‖ := by
    rw [norm_mul]
    exact mul_le_of_le_one_right hz0.le hk00
  have hr01 : ‖z * k 0 1‖ ≤ ‖z‖ := by
    rw [norm_mul]
    exact mul_le_of_le_one_right hz0.le hk01
  refine { bot := ?_, top := ?_, form := ?_, detC_ne := ?_, rho_pos := hz0, norm_det := hnorm }
  · intro j
    fin_cases j
    · simpa [p10] using hk10
    · simpa [p11] using hk11
  · intro j
    fin_cases j
    · simpa [p00] using hr00
    · simpa [p01] using hr01
  · intro x t
    refine qForm_eq_of_rows ?_ ?_ ?_ ?_ x t
    · rw [p00, p01]
      calc z * k 0 0 * conj (z * k 0 0) + z * k 0 1 * conj (z * k 0 1)
          = z * conj z * (k 0 0 * conj (k 0 0) + k 0 1 * conj (k 0 1)) := by
            simp only [map_mul]
            ring
        _ = ((‖z‖ ^ 2 : ℝ) : ℂ) := by rw [r0, mul_one, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    · rw [p10, p11]
      exact r1
    · rw [p00, p01, p10, p11]
      linear_combination z * r01
    · rw [p00, p01, p10, p11]
      simp only [map_mul]
      linear_combination conj z * r10
  · rw [← norm_pos_iff, hnorm]
    exact hz0

private theorem ne_zero_of_one_le_norm {z : ℂ} (hz : 1 ≤ ‖z‖) : z ≠ 0 := norm_pos_iff.mp (zero_lt_one.trans_le hz)

section Fields

variable {F : Freq} {χ : ℂ → ℂ} {A : ℕ} {W : Matrix (Fin 2) (Fin 2) ℂ → ℂ}

private theorem field_smooth (hχ : Measurable χ) (hχA : ∀ t : ℂ, t ≠ 0 → ‖χ t‖ ≤ ‖t‖ ^ A + ‖t‖⁻¹ ^ A)
    (hW : AgreesWith (InClsC F χ) glSet (asPi W)) : ContDiffOn ℝ (⊤ : ℕ∞) (asPi W) glSet :=
  InClsC.contDiffOn_of_agreesWith hχ hχA isOpen_glSet detC_ne_of_mem_glSet hW

private theorem field_decay_top (hχ : Measurable χ) (hχA : ∀ t : ℂ, t ≠ 0 → ‖χ t‖ ≤ ‖t‖ ^ A + ‖t‖⁻¹ ^ A)
    (hW : AgreesWith (InClsC F χ) glSet (asPi W)) :
    ∀ (j N : ℕ), ∃ C : ℝ, ∀ (z : ℂ) (k : Matrix (Fin 2) (Fin 2) ℂ), IsK k → 1 ≤ ‖z‖ →
      ‖iteratedFDerivWithin ℝ j (asPi W) glSet (diagOneMulCoords z k)‖ ≤ C * ‖z‖ ^ (-(N : ℝ)) := by
  intro j N
  obtain ⟨C, hC⟩ := InClsC.decay_top_of_agreesWith hχ hχA isOpen_glSet detC_ne_of_mem_glSet hW
    (ι := {p : ℂ × Matrix (Fin 2) (Fin 2) ℂ // IsK p.2 ∧ 1 ≤ ‖p.1‖}) (fun i => diagOneMulCoords i.1.1 i.1.2)
    (fun i => ‖i.1.1‖) (fun i => mem_glSet_diagOneMulCoords (ne_zero_of_one_le_norm i.2.2) i.2.1)
    (fun i => isGatePt_diagOneMulCoords (ne_zero_of_one_le_norm i.2.2) i.2.1) (fun i => i.2.2) j N
  exact ⟨C, fun z k hk hz => hC ⟨(z, k), hk, hz⟩⟩

private theorem field_decay_zero (hχ : Measurable χ) (hχA : ∀ t : ℂ, t ≠ 0 → ‖χ t‖ ≤ ‖t‖ ^ A + ‖t‖⁻¹ ^ A)
    (hW : AgreesWith (InClsC F χ) glSet (asPi W)) :
    ∀ j : ℕ, ∃ (C σ : ℝ), ∀ (z : ℂ) (k : Matrix (Fin 2) (Fin 2) ℂ), IsK k → z ≠ 0 → ‖z‖ ≤ 1 →
      ‖iteratedFDerivWithin ℝ j (asPi W) glSet (diagOneMulCoords z k)‖ ≤ C * ‖z‖ ^ (-σ) := by
  intro j
  obtain ⟨C, n, hC⟩ := InClsC.decay_zero_of_agreesWith hχ hχA isOpen_glSet detC_ne_of_mem_glSet hW
    (ι := {p : ℂ × Matrix (Fin 2) (Fin 2) ℂ // IsK p.2 ∧ p.1 ≠ 0 ∧ ‖p.1‖ ≤ 1}) (fun i => diagOneMulCoords i.1.1 i.1.2)
    (fun i => ‖i.1.1‖) (fun i => mem_glSet_diagOneMulCoords i.2.2.1 i.2.1)
    (fun i => isGatePt_diagOneMulCoords i.2.2.1 i.2.1) (fun i => i.2.2.2) j
  exact ⟨C, (n : ℝ), fun z k hk hz0 hz1 => hC ⟨(z, k), hk, hz0, hz1⟩⟩

end Fields
p2m_reactivate "P2MW.S_LanglandsTunnell_Converse_exists_archDatumC_W_ne_zero.ArchEngineC"

private theorem IsPoly.pow {P : X₄ℂ → ℂ → ℂ → ℂ} (h : IsPoly P) (n : ℕ) : IsPoly fun m x Y => P m x Y ^ n := by
  induction n with
  | zero =>
    refine (IsPoly.const 1).congr ?_
    funext m x Y
    simp
  | succ n ih =>
    refine (ih.mul h).congr ?_
    funext m x Y
    simp [pow_succ]

private def memberQ (P : LanglandsTunnell.ComplexArchParam) (m : X₄ℂ) (x Y : ℂ) : ℂ :=
  conj (-(Y * m 0 0 + x * m 1 0)) ^ P.k₁.toNat * (-(Y * m 0 0 + x * m 1 0)) ^ (-P.k₁).toNat *
    (conj (-(Y * m 0 1 + x * m 1 1)) ^ (-P.k₂).toNat * (-(Y * m 0 1 + x * m 1 1)) ^ (- -P.k₂).toNat)

private theorem isPoly_memberQ (P : LanglandsTunnell.ComplexArchParam) : IsPoly (memberQ P) := by
  have h0 : IsPoly fun m x Y => -(Y * m 0 0 + x * m 1 0) :=
    ((IsPoly.rowZeroY 0).add (IsPoly.varX.mul (IsPoly.rowOne 0))).neg
  have h1 : IsPoly fun m x Y => -(Y * m 0 1 + x * m 1 1) :=
    ((IsPoly.rowZeroY 1).add (IsPoly.varX.mul (IsPoly.rowOne 1))).neg
  exact ((h0.conj_mem.pow _).mul (h0.pow _)).mul ((h1.conj_mem.pow _).mul (h1.pow _))

private theorem psiC_eq (P : LanglandsTunnell.ComplexArchParam) (m : X₄ℂ) (x Y : ℂ) :
    PsiC P (Matrix.of m) x Y = phiFam (memberQ P) m x Y := by
  simp only [PsiC, complexTestFun, Matrix.of_apply, phiFam, memberQ, gaussW]
  have hE : Complex.exp (-(2 * (Real.pi : ℂ) * ((‖-(Y * m 0 0 + x * m 1 0)‖ : ℝ) : ℂ) ^ 2)) *
      Complex.exp (-(2 * (Real.pi : ℂ) * ((‖-(Y * m 0 1 + x * m 1 1)‖ : ℝ) : ℂ) ^ 2)) = Complex.exp (expo m x Y) := by
    rw [← Complex.exp_add, expo, norm_neg, norm_neg, ← TateComplex.Datum.ofReal_norm_sq_eq_mul_conj,
      ← TateComplex.Datum.ofReal_norm_sq_eq_mul_conj]
    congr 1
    push_cast
    ring
  linear_combination (conj (-(Y * m 0 0 + x * m 1 0)) ^ P.k₁.toNat * (-(Y * m 0 0 + x * m 1 0)) ^ (-P.k₁).toNat *
    (conj (-(Y * m 0 1 + x * m 1 1)) ^ (-P.k₂).toNat * (-(Y * m 0 1 + x * m 1 1)) ^ (- -P.k₂).toNat)) * hE

private theorem psi_neg_mul_eq_fkerC (s w : ℂ) : psi (-(s * w)) = fkerC (2 * conj s) w := by
  unfold psi fkerC
  congr 1
  rw [Complex.inner]
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  ring

private def memberFreq : Freq where
  fr t := 2 * conj t⁻¹
  c := 2
  c_pos := two_pos
  norm_fr t _ := by simp
  measurable_fr := (Complex.continuous_conj.measurable.comp measurable_inv).const_mul 2
  jac := 1

private theorem innerWC_eq (P : LanglandsTunnell.ComplexArchParam) (m : X₄ℂ) {t : ℂ} (ht : t ≠ 0) :
    innerWC P (Matrix.of m) t = innFC memberFreq (memberQ P) m t := by
  set Φ : ℂ → ℂ := fun w => PsiC P (Matrix.of m) w t * psi (-(t⁻¹ * w)) with hΦ
  have hpt : (fun z : ℂ => complexTestFun P.k₁ (-(t * (Matrix.of m 0 0 + z * Matrix.of m 1 0))) *
      complexTestFun (-P.k₂) (-(t * (Matrix.of m 0 1 + z * Matrix.of m 1 1))) * psi (-z)) = fun z => Φ (t * z) := by
    funext z
    have e0 : -(t * (m 0 0 + z * m 1 0)) = -(t * m 0 0 + t * z * m 1 0) := by ring
    have e1 : -(t * (m 0 1 + z * m 1 1)) = -(t * m 0 1 + t * z * m 1 1) := by ring
    simp only [hΦ, PsiC, Matrix.of_apply, inv_mul_cancel_left₀ ht, e0, e1]
  have hΦ' : Φ = fun w => fkerC (memberFreq.fr t) w * phiFam (memberQ P) m w t := by
    funext w
    show PsiC P (Matrix.of m) w t * psi (-(t⁻¹ * w)) = _
    rw [show memberFreq.fr t = 2 * conj t⁻¹ from rfl, psiC_eq, psi_neg_mul_eq_fkerC,
      mul_comm (phiFam (memberQ P) m w t)]
  rw [innerWC, hpt, TateComplex.integral_comp_mul_left_C Φ t, hΦ', ← fourier_eq_C, innFC, Complex.real_smul]
  congr 1
  rw [show memberFreq.jac = (1 : ℝ) from rfl, one_mul, inv_pow]

private theorem asPi_wmemC_eq (P : LanglandsTunnell.ComplexArchParam) (m : X₄ℂ) :
    asPi (WmemC P) m = ((‖detC m‖ ^ 2 : ℝ) : ℂ) * quasiChar P.u₁ P.k₁ (detC m) *
      tIntC memberFreq (memberQ P) (quasiChar (P.u₁ - P.u₂) (P.k₁ - P.k₂)) m := by
  rw [asPi, WmemC, ← detC_eq_det]
  congr 1
  rw [tIntC]
  refine integral_congr_ae (ae_ne_zero_C.mono fun t ht => ?_)
  beta_reduce
  rw [innerWC_eq P m ht]
  exact mul_comm _ _

private theorem ofReal_norm_pow_eq_cpow {d : ℂ} (hd : d ≠ 0) (n : ℕ) :
    ((‖d‖ : ℝ) : ℂ) ^ n = ((‖d‖ ^ 2 : ℝ) : ℂ) ^ ((n : ℂ) / 2) := by
  have hx : (0 : ℝ) ≤ ‖d‖ ^ 2 := by positivity
  have hr : (‖d‖ ^ 2) ^ ((n : ℝ) / 2) = ‖d‖ ^ n := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg d)]
    congr 1
    ring
  have h2 : (((n : ℝ) / 2 : ℝ) : ℂ) = (n : ℂ) / 2 := by simp
  rw [← h2, ← Complex.ofReal_cpow hx, hr]
  exact (Complex.ofReal_pow ‖d‖ n).symm

private theorem cpow_beta_eq {N : ℂ} (hN : N ≠ 0) (u : ℂ) (n : ℕ) :
    N ^ (1 + u - (n : ℂ) / 2) = N * N ^ u * (N ^ ((n : ℂ) / 2))⁻¹ := by
  rw [show 1 + u - (n : ℂ) / 2 = 1 + u + -((n : ℂ) / 2) by ring, Complex.cpow_add _ _ hN, Complex.cpow_add _ _ hN,
    Complex.cpow_one, Complex.cpow_neg]

private theorem prefactor_eq_of_nonneg (u : ℂ) {d : ℂ} (hd : d ≠ 0) (n : ℕ) :
    ((‖d‖ ^ 2 : ℝ) : ℂ) * quasiChar u (n : ℤ) d = d ^ n * ((‖d‖ ^ 2 : ℝ) : ℂ) ^ (1 + u - (n : ℂ) / 2) := by
  have hN : ((‖d‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (pow_pos (norm_pos_iff.mpr hd) 2).ne'
  rw [TateComplex.Datum.quasiChar_eq_sq_cpow u _ hd, zpow_natCast, div_pow, ofReal_norm_pow_eq_cpow hd n,
    cpow_beta_eq hN u n]
  ring

private theorem prefactor_eq_of_nonpos (u : ℂ) {d : ℂ} (hd : d ≠ 0) (n : ℕ) :
    ((‖d‖ ^ 2 : ℝ) : ℂ) * quasiChar u (-(n : ℤ)) d = conj d ^ n * ((‖d‖ ^ 2 : ℝ) : ℂ) ^ (1 + u - (n : ℂ) / 2) := by
  have hN : ((‖d‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (pow_pos (norm_pos_iff.mpr hd) 2).ne'
  have hM : ((‖d‖ ^ 2 : ℝ) : ℂ) ^ ((n : ℂ) / 2) * ((‖d‖ ^ 2 : ℝ) : ℂ) ^ ((n : ℂ) / 2) =
      ((‖d‖ ^ 2 : ℝ) : ℂ) ^ n := by
    rw [← Complex.cpow_add _ _ hN, show (n : ℂ) / 2 + (n : ℂ) / 2 = (n : ℂ) by ring, Complex.cpow_natCast]
  have hdc : d ^ n * conj d ^ n = ((‖d‖ ^ 2 : ℝ) : ℂ) ^ n := by
    rw [← mul_pow, TateComplex.Datum.ofReal_norm_sq_eq_mul_conj]
  have hM0 : ((‖d‖ ^ 2 : ℝ) : ℂ) ^ ((n : ℂ) / 2) ≠ 0 := by
    intro h
    rw [h, zero_mul] at hM
    exact pow_ne_zero n hN hM.symm
  have key : (d ^ n / ((‖d‖ ^ 2 : ℝ) : ℂ) ^ ((n : ℂ) / 2))⁻¹ = conj d ^ n / ((‖d‖ ^ 2 : ℝ) : ℂ) ^ ((n : ℂ) / 2) := by
    rw [inv_div, div_eq_div_iff (pow_ne_zero n hd) hM0]
    linear_combination hM - hdc
  rw [TateComplex.Datum.quasiChar_eq_sq_cpow u _ hd, zpow_neg, zpow_natCast, div_pow, ofReal_norm_pow_eq_cpow hd n,
    key, cpow_beta_eq hN u n]
  ring

private theorem agreesWith_wmemC (P : LanglandsTunnell.ComplexArchParam) :
    AgreesWith (InClsC memberFreq (quasiChar (P.u₁ - P.u₂) (P.k₁ - P.k₂))) glSet (asPi (WmemC P)) := by
  obtain ⟨n, hn | hn⟩ := Int.eq_nat_or_neg P.k₁
  · refine ⟨_, InClsC.term (isEntryPoly_detC.pow n) (1 + P.u₁ - (n : ℂ) / 2) (isPoly_memberQ P), fun m hm => ?_⟩
    have hd : detC m ≠ 0 := detC_ne_of_mem_glSet m hm
    show asPi (WmemC P) m = detC m ^ n * detNormPow (1 + P.u₁ - (n : ℂ) / 2) m *
      tIntC memberFreq (memberQ P) (quasiChar (P.u₁ - P.u₂) (P.k₁ - P.k₂)) m
    rw [asPi_wmemC_eq, detNormPow]
    congr 1
    rw [hn]
    exact prefactor_eq_of_nonneg P.u₁ hd n
  · refine ⟨_, InClsC.term (isEntryPoly_detC.conj_mem.pow n) (1 + P.u₁ - (n : ℂ) / 2) (isPoly_memberQ P),
      fun m hm => ?_⟩
    have hd : detC m ≠ 0 := detC_ne_of_mem_glSet m hm
    show asPi (WmemC P) m = conj (detC m) ^ n * detNormPow (1 + P.u₁ - (n : ℂ) / 2) m *
      tIntC memberFreq (memberQ P) (quasiChar (P.u₁ - P.u₂) (P.k₁ - P.k₂)) m
    rw [asPi_wmemC_eq, detNormPow]
    congr 1
    rw [hn]
    exact prefactor_eq_of_nonpos P.u₁ hd n

private theorem wmemC_smooth (P : LanglandsTunnell.ComplexArchParam) : ContDiffOn ℝ (⊤ : ℕ∞) (asPi (WmemC P)) glSet :=
  field_smooth (measurable_quasiChar _ _) (norm_quasiChar_le (P.u₁ - P.u₂) (P.k₁ - P.k₂)) (agreesWith_wmemC P)

private theorem wmemC_decay_top (P : LanglandsTunnell.ComplexArchParam) :
    ∀ (j N : ℕ), ∃ C : ℝ, ∀ (z : ℂ) (k : Matrix (Fin 2) (Fin 2) ℂ), IsK k → 1 ≤ ‖z‖ →
      ‖iteratedFDerivWithin ℝ j (asPi (WmemC P)) glSet (diagOneMulCoords z k)‖ ≤ C * ‖z‖ ^ (-(N : ℝ)) :=
  field_decay_top (measurable_quasiChar _ _) (norm_quasiChar_le (P.u₁ - P.u₂) (P.k₁ - P.k₂)) (agreesWith_wmemC P)

private theorem wmemC_decay_zero (P : LanglandsTunnell.ComplexArchParam) :
    ∀ j : ℕ, ∃ (C σ : ℝ), ∀ (z : ℂ) (k : Matrix (Fin 2) (Fin 2) ℂ), IsK k → z ≠ 0 → ‖z‖ ≤ 1 →
      ‖iteratedFDerivWithin ℝ j (asPi (WmemC P)) glSet (diagOneMulCoords z k)‖ ≤ C * ‖z‖ ^ (-σ) :=
  field_decay_zero (measurable_quasiChar _ _) (norm_quasiChar_le (P.u₁ - P.u₂) (P.k₁ - P.k₂)) (agreesWith_wmemC P)

end ArchEngineC
p2m_reactivate "P2MW.S_LanglandsTunnell_Converse_exists_archDatumC_W_ne_zero.ArchEngineC"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Converse_exists_archDatumC_W_ne_zero.ArchEngineC"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Converse_exists_archDatumC_W_ne_zero.ArchEngineC"

section

open Complex MeasureTheory LanglandsTunnell LanglandsTunnell.ArchPlace LanglandsTunnell.Converse.ArchC
p2m_open "TateComplex.W3C P2MW.S_LanglandsTunnell_Converse_exists_archDatumC_W_ne_zero.TateComplex.W3C"

noncomputable section

namespace TateComplex
namespace Datum

variable (P : ComplexArchParam)

private theorem complexTestFun_neg (k : ℤ) (v : ℂ) : complexTestFun k (-v) = (-1) ^ k.natAbs * complexTestFun k v := by
  unfold complexTestFun
  rw [norm_neg, map_neg (starRingEnd ℂ) v, neg_eq_neg_one_mul (starRingEnd ℂ v), neg_eq_neg_one_mul v, mul_pow,
    mul_pow, ← Int.toNat_add_toNat_neg_eq_natAbs k, pow_add]
  ring

private theorem PsiC_one (z t : ℂ) : PsiC P 1 z t = complexTestFun P.k₁ (-t) * complexTestFun (-P.k₂) (-z) := by
  simp [PsiC]

private theorem FC_const_mul_apply (c : ℂ) (f : ℂ → ℂ) (w : ℂ) : FC (fun z => c * f z) w = c * FC f w :=
  congrFun (FC_const_mul c f) w

private theorem FC_complexTestFun_apply (k : ℤ) (w : ℂ) : FC (complexTestFun k) w = cC k * complexTestFun (-k) w :=
  congrFun (FC_complexTestFun k) w

private theorem F₁C_PsiC_one (ξ t : ℂ) :
    W3C.F₁C (PsiC P 1) ξ t
      = complexTestFun P.k₁ (-t) * ((-1) ^ P.k₂.natAbs * cC (-P.k₂) * complexTestFun P.k₂ (starRingEnd ℂ ξ)) := by
  have hfun : (fun z => PsiC P 1 z t)
      = fun z => complexTestFun P.k₁ (-t) * ((-1) ^ P.k₂.natAbs * complexTestFun (-P.k₂) z) := by
    funext z
    rw [PsiC_one, complexTestFun_neg (-P.k₂), Int.natAbs_neg]
  rw [W3C.F₁C, hfun, FC_const_mul_apply, FC_const_mul_apply, FC_complexTestFun_apply, neg_neg]
  ring

private theorem ZC_of_product {Ψ : ℂ → ℂ → ℂ} (hΨ : ClsC Ψ) (A B : ℂ → ℂ) (hAB : ∀ ξ t, Ψ ξ t = A t * B ξ) (m₁ m₂ : ℤ)
    {w₁ w₂ : ℂ} (h₁ : 0 < w₁.re) (h₂ : 0 < w₂.re) :
    ZC Ψ m₁ m₂ w₁ w₂ = tateZetaC B m₁ w₁ * tateZetaC A m₂ w₂ := by
  rw [hΨ.ZC_eq_iterated m₁ m₂ h₁ h₂]
  have e : (fun t : ℂ => tateZetaC (fun ξ => Ψ ξ t) m₁ w₁ * kerC m₂ w₂ t)
      = fun t : ℂ => tateZetaC B m₁ w₁ * (A t * kerC m₂ w₂ t) := by
    funext t
    simp only [hAB]
    rw [tateZetaC_const_mul']
    ring
  rw [e, integral_const_mul, tateZetaC_eq_integral_ker A m₂ w₂]

private theorem tateZetaC_complexTestFun_neg (k : ℤ) {w : ℂ} (hw : 0 < w.re) :
    tateZetaC (fun t => complexTestFun k (-t)) k w
      = (-1) ^ k.natAbs * ((Real.pi / 2 : ℂ) * Gammaℂ (w + (k.natAbs : ℂ) / 2)) := by
  have e : (fun t => complexTestFun k (-t)) = fun t => (-1) ^ k.natAbs * complexTestFun k t := by
    funext t
    exact complexTestFun_neg k t
  rw [e, tateZetaC_const_mul', tateZetaC_complexTestFun k hw]

private theorem tateZetaC_const_mul_comp_conj (c : ℂ) (k : ℤ) {w : ℂ} (hw : 0 < w.re) :
    tateZetaC (fun ξ => c * complexTestFun k (starRingEnd ℂ ξ)) (-k) w
      = c * ((Real.pi / 2 : ℂ) * Gammaℂ (w + (k.natAbs : ℂ) / 2)) := by
  rw [tateZetaC_const_mul', tateZetaC_comp_conj, neg_neg, tateZetaC_complexTestFun k hw]

private theorem ZC_F₁C_PsiC_one_ne_zero {w₁ w₂ : ℂ} (h₁ : 0 < w₁.re) (h₂ : 0 < w₂.re) :
    ZC (W3C.F₁C (PsiC P 1)) (-P.k₂) P.k₁ w₁ w₂ ≠ 0 := by
  have hcls : ClsC (W3C.F₁C (PsiC P 1)) := (clsC_PsiC P (by simp)).F₁C
  rw [ZC_of_product hcls (fun t => complexTestFun P.k₁ (-t))
    (fun ξ => ((-1) ^ P.k₂.natAbs * cC (-P.k₂)) * complexTestFun P.k₂ (starRingEnd ℂ ξ)) (F₁C_PsiC_one P)
    (-P.k₂) P.k₁ h₁ h₂, tateZetaC_const_mul_comp_conj _ _ h₁, tateZetaC_complexTestFun_neg _ h₂]
  have hneg : ((-1 : ℂ)) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  have hpi : (Real.pi / 2 : ℂ) ≠ 0 := div_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne') two_ne_zero
  exact mul_ne_zero
    (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hneg) (cC_ne_zero _)) (mul_ne_zero hpi (Gammaℂ_shift_ne_zero h₁ _)))
    (mul_ne_zero (pow_ne_zero _ hneg) (mul_ne_zero hpi (Gammaℂ_shift_ne_zero h₂ _)))

private theorem normalizer_one : normalizer P 1 = 1 := by
  simp [normalizer, quasiChar_one]

private theorem WmemC_eq_zero_of_det_eq_zero {g : Matrix (Fin 2) (Fin 2) ℂ} (hg : g.det = 0) : WmemC P g = 0 := by
  unfold WmemC
  rw [hg]
  simp

private theorem exists_WmemC_diagOne_ne_zero : ∃ y : ℂ, WmemC P (diagOne y) ≠ 0 := by
  by_contra h
  push Not at h
  set s : ℂ := ((max (-P.u₁.re) (-P.u₂.re) + 1 : ℝ) : ℂ) with hs
  have habs : max (-P.u₁.re) (-P.u₂.re) < s.re + (0 : ℂ).re := by
    simp only [hs, Complex.ofReal_re, Complex.zero_re, add_zero]
    exact lt_add_one _
  obtain ⟨h₁, h₂⟩ := re_pos_of_abscissa_lt P habs
  have hbridge := integral_zetaIntegrand_WmemC P 1 0 s 0 (by simp) h₁ h₂
  have hzero : (∫ y : ℂ, zetaIntegrand (WmemC P) 1 0 0 s y) = 0 := by
    have e : (fun y : ℂ => zetaIntegrand (WmemC P) 1 0 0 s y) = fun _ => 0 := by
      funext y
      simp [zetaIntegrand, h]
    rw [e, integral_zero]
  rw [hzero, normalizer_one, one_mul, zero_add, zero_add] at hbridge
  exact ZC_F₁C_PsiC_one_ne_zero P h₂ h₁ hbridge.symm

private theorem exists_WmemC_GL_ne_zero : ∃ g : GL (Fin 2) ℂ, WmemC P (g : Matrix (Fin 2) (Fin 2) ℂ) ≠ 0 := by
  obtain ⟨y, hy⟩ := exists_WmemC_diagOne_ne_zero P
  have hdet : (diagOne y).det ≠ 0 := fun hd => hy (WmemC_eq_zero_of_det_eq_zero P hd)
  exact ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (diagOne y) hdet, hy⟩

end TateComplex.Datum
p2m_reactivate "P2MW.S_LanglandsTunnell_Converse_exists_archDatumC_W_ne_zero.ArchEngineC"
p2m_reactivate "P2MW.S_LanglandsTunnell_Converse_exists_archDatumC_W_ne_zero.ArchEngineC"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Converse_exists_archDatumC_W_ne_zero.ArchEngineC"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Converse_exists_archDatumC_W_ne_zero.ArchEngineC"

section

open Complex MeasureTheory LanglandsTunnell LanglandsTunnell.ArchPlace LanglandsTunnell.Converse.ArchC
p2m_open "TateComplex.W3C P2MW.S_LanglandsTunnell_Converse_exists_archDatumC_W_ne_zero.TateComplex.W3C"

noncomputable section

namespace TateComplex
namespace Datum

variable (P : ComplexArchParam)

private def zetaEntC (g : Matrix (Fin 2) (Fin 2) ℂ) (u : ℂ) (k : ℤ) (s : ℂ) : ℂ :=
  normalizer P g * EC (W3C.F₁C (PsiC P g)) (-(k + P.k₂)) (k + P.k₁) (s + u + P.u₂) (s + u + P.u₁)

private theorem zetaIntegrable_WmemC (g : Matrix (Fin 2) (Fin 2) ℂ) (u : ℂ) (k : ℤ) (s : ℂ) (hg : g.det ≠ 0)
    (hs : max (-P.u₁.re) (-P.u₂.re) < s.re + u.re) : Integrable (zetaIntegrand (WmemC P) g u k s) := by
  obtain ⟨h₁, h₂⟩ := re_pos_of_abscissa_lt P hs
  have e : zetaIntegrand (WmemC P) g u k s = fun y => ∫ t : ℂ, zint2 P g u s k (y, t) :=
    funext (zetaIntegrand_eq_integral_zint2 P g u s k)
  rw [e]
  exact (integrable_zint2 P g u s k hg h₁ h₂).integral_prod_left

private theorem zetaEq_WmemC (g : Matrix (Fin 2) (Fin 2) ℂ) (u : ℂ) (k : ℤ) (s : ℂ) (hg : g.det ≠ 0)
    (hs : max (-P.u₁.re) (-P.u₂.re) < s.re + u.re) :
    ∫ z : ℂ, zetaIntegrand (WmemC P) g u k s z = (P.twist u k).archFactor s * zetaEntC P g u k s := by
  obtain ⟨h₁, h₂⟩ := re_pos_of_abscissa_lt P hs
  rw [integral_zetaIntegrand_WmemC P g u s k hg h₁ h₂, ZC_eq_EC _ _ _ h₂ h₁, archFactor_twist', zetaEntC,
    Int.natAbs_neg]
  ring

private theorem zetaEntC_of_det_eq_zero {g : Matrix (Fin 2) (Fin 2) ℂ} (hg : g.det = 0) (u : ℂ) (k : ℤ) :
    zetaEntC P g u k = fun _ => 0 := by
  funext s
  simp [zetaEntC, normalizer, hg]

private theorem zetaEntC_differentiable (g : Matrix (Fin 2) (Fin 2) ℂ) (u : ℂ) (k : ℤ) :
    Differentiable ℂ (zetaEntC P g u k) := by
  by_cases hg : g.det = 0
  · rw [zetaEntC_of_det_eq_zero P hg]
    exact differentiable_const 0
  · have h := (clsC_PsiC P hg).F₁C.differentiable_EC_comp (-(k + P.k₂)) (k + P.k₁)
      (f₁ := fun s => s + u + P.u₂) (f₂ := fun s => s + u + P.u₁) 1 (u + P.u₂) 1 (u + P.u₁)
      (fun w => by ring) (fun w => by ring)
    exact h.const_mul (normalizer P g)

end TateComplex.Datum
p2m_reactivate "P2MW.S_LanglandsTunnell_Converse_exists_archDatumC_W_ne_zero.ArchEngineC"
p2m_reactivate "P2MW.S_LanglandsTunnell_Converse_exists_archDatumC_W_ne_zero.ArchEngineC"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Converse_exists_archDatumC_W_ne_zero.ArchEngineC"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Converse_exists_archDatumC_W_ne_zero.ArchEngineC"

section

open Complex MeasureTheory LanglandsTunnell LanglandsTunnell.ArchPlace LanglandsTunnell.Converse.ArchC
p2m_open "TateComplex.W3C P2MW.S_LanglandsTunnell_Converse_exists_archDatumC_W_ne_zero.TateComplex.W3C"

noncomputable section

namespace TateComplex
namespace Datum

variable (P : ComplexArchParam)

private theorem zetaEntC_finiteOrder (g : Matrix (Fin 2) (Fin 2) ℂ) (u : ℂ) (k : ℤ) (A B : ℝ) :
    ∃ C D : ℝ, ∀ s : ℂ, A ≤ s.re → s.re ≤ B → ‖zetaEntC P g u k s‖ ≤ C * Real.exp (D * |s.im|) := by
  by_cases hg : g.det = 0
  · refine ⟨0, 0, fun s _ _ => ?_⟩
    rw [zetaEntC_of_det_eq_zero P hg]
    simp
  · obtain ⟨A', B', hb⟩ :=
      (clsC_PsiC P hg).F₁C.exists_EC_strip_bound (-(k + P.k₂)) (k + P.k₁) (u + P.u₂) (u + P.u₁) A B
    refine ⟨‖normalizer P g‖ * A', B', fun s h₁ h₂ => ?_⟩
    have e : zetaEntC P g u k s
        = normalizer P g * EC (W3C.F₁C (PsiC P g)) (-(k + P.k₂)) (k + P.k₁) (s + (u + P.u₂)) (s + (u + P.u₁)) := by
      simp only [zetaEntC, add_assoc]
    rw [e, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hb s h₁ h₂) (norm_nonneg _)

private theorem PsiC_weyl_mul (g : Matrix (Fin 2) (Fin 2) ℂ) : PsiC P (weyl * g) = fun z t => PsiC P g t (-z) := by
  obtain ⟨h00, h01, h10, h11⟩ := weyl_mul_entries g
  funext z t
  simp only [PsiC, h00, h01, h10, h11]
  ring_nf

private theorem normalizer_weyl_mul (g : Matrix (Fin 2) (Fin 2) ℂ) : normalizer P (weyl * g) = normalizer P g := by
  simp [normalizer, det_weyl]

private theorem neg_one_zpow_eq_pow_natAbs (m : ℤ) : (-1 : ℂ) ^ m = (-1 : ℂ) ^ m.natAbs := by
  rcases Int.eq_nat_or_neg m with ⟨n, rfl | rfl⟩
  · simp
  · rw [zpow_neg, zpow_natCast, Int.natAbs_neg, Int.natAbs_natCast, ← inv_pow, inv_neg_one]

private theorem cC_mul_inv_eq_epsilon (u : ℂ) (k : ℤ) :
    cC (k + P.k₁) * ((-1 : ℂ) ^ (k + P.k₁))⁻¹ = (P.twist u k).epsilonFactor * cC (-(k + P.k₂)) := by
  rw [epsilonFactor_twist, cC, cC, Int.natAbs_neg (k + P.k₂), neg_one_zpow_eq_pow_natAbs,
    neg_pow I (k + P.k₁).natAbs]
  have h1 : ((-1 : ℂ) ^ (k + P.k₁).natAbs) ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  have h3 : (-1 : ℂ) ^ (k + P.k₁).natAbs * ((-1 : ℂ) ^ (k + P.k₁).natAbs)⁻¹ = 1 := mul_inv_cancel₀ h1
  have h2 : I ^ (k + P.k₂).natAbs * (-I) ^ (k + P.k₂).natAbs = 1 := by
    rw [← mul_pow]
    simp
  linear_combination (I ^ (k + P.k₁).natAbs / 2) * h3 - (I ^ (k + P.k₁).natAbs / 2) * h2

private theorem norm_neg_one' : ‖(-1 : ℂ)‖ = 1 := by simp

private theorem zetaEntC_functional_equation (g : Matrix (Fin 2) (Fin 2) ℂ) (u : ℂ) (k : ℤ) (s : ℂ) (hg : g.det ≠ 0) :
    zetaEntC P (weyl * g) (-(u + P.centralExponent)) (-(k + P.centralTwist)) (1 - s)
      = (P.twist u k).epsilonFactor * zetaEntC P g u k s := by
  have hΨ : ClsC (PsiC P g) := clsC_PsiC P hg
  have hΦ : ClsC (fun z t => PsiC P g t (-z)) := hΨ.swap.reflZ
  have hi₁ : -(-(k + P.centralTwist) + P.k₂) = k + P.k₁ := by rw [centralTwist_eq]; ring
  have hi₂ : -(k + P.centralTwist) + P.k₁ = -(k + P.k₂) := by rw [centralTwist_eq]; ring
  have hp₁ : 1 - s + -(u + P.centralExponent) + P.u₂ = 1 - (s + u + P.u₁) := by rw [centralExponent_eq]; ring
  have hp₂ : 1 - s + -(u + P.centralExponent) + P.u₁ = 1 - (s + u + P.u₂) := by rw [centralExponent_eq]; ring
  have eΦ : (fun z t => PsiC P g t (-z)) = fun z t => PsiC P g t (-1 * z) := by
    funext z t
    rw [neg_one_mul]
  have hF : EC (W3C.F₁C (PsiC P g)) (-(k + P.k₂)) (k + P.k₁) (1 - (1 - (s + u + P.u₂))) (s + u + P.u₁)
      = cC (-(k + P.k₂)) * EC (PsiC P g) (-(k + P.k₂)) (k + P.k₁) (1 - (s + u + P.u₂)) (s + u + P.u₁) :=
    hΨ.EC_F₁C _ _ _ _
  rw [sub_sub_cancel] at hF
  rw [zetaEntC, zetaEntC, hi₁, hi₂, hp₁, hp₂, normalizer_weyl_mul, PsiC_weyl_mul, hΦ.EC_F₁C, hF]
  rw [eΦ] at hΦ ⊢
  rw [hΨ.swap.EC_rot norm_neg_one' (k + P.k₁) (-(k + P.k₂)) (s + u + P.u₁) (1 - (s + u + P.u₂)),
    hΨ.EC_swap (-(k + P.k₂)) (k + P.k₁) (1 - (s + u + P.u₂)) (s + u + P.u₁)]
  linear_combination
    (normalizer P g * EC (PsiC P g) (-(k + P.k₂)) (k + P.k₁) (1 - (s + u + P.u₂)) (s + u + P.u₁))
      * cC_mul_inv_eq_epsilon P u k

end TateComplex.Datum
p2m_reactivate "P2MW.S_LanglandsTunnell_Converse_exists_archDatumC_W_ne_zero.ArchEngineC"
p2m_reactivate "P2MW.S_LanglandsTunnell_Converse_exists_archDatumC_W_ne_zero.ArchEngineC"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Converse_exists_archDatumC_W_ne_zero.ArchEngineC"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Converse_exists_archDatumC_W_ne_zero.ArchEngineC"

section

open LanglandsTunnell LanglandsTunnell.Converse LanglandsTunnell.Converse.ArchC

noncomputable section

namespace TateComplex
namespace Datum

variable (P : ComplexArchParam)

private def datumC : ArchDatumC P where
  W := WmemC P
  smooth := ArchEngineC.wmemC_smooth P
  unip_law := WmemC_unip P
  central_law := WmemC_central P
  zetaEntire := zetaEntC P
  zetaEntire_differentiable := zetaEntC_differentiable P
  zeta_abscissa := max (-P.u₁.re) (-P.u₂.re)
  zeta_integrable := zetaIntegrable_WmemC P
  zeta_eq := zetaEq_WmemC P
  functional_equation := zetaEntC_functional_equation P
  zetaEntire_finiteOrder := zetaEntC_finiteOrder P
  decay_top := ArchEngineC.wmemC_decay_top P
  decay_zero := ArchEngineC.wmemC_decay_zero P

private theorem exists_archDatumC_WmemC : ∃ D : ArchDatumC P, ∃ g : GL (Fin 2) ℂ, D.W g ≠ 0 := by
  obtain ⟨g, hg⟩ := exists_WmemC_GL_ne_zero P
  exact ⟨datumC P, g, hg⟩

end TateComplex.Datum
p2m_reactivate "P2MW.S_LanglandsTunnell_Converse_exists_archDatumC_W_ne_zero.ArchEngineC"
p2m_reactivate "P2MW.S_LanglandsTunnell_Converse_exists_archDatumC_W_ne_zero.ArchEngineC"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Converse_exists_archDatumC_W_ne_zero.ArchEngineC"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Converse_exists_archDatumC_W_ne_zero.ArchEngineC"

open LanglandsTunnell LanglandsTunnell.Converse in

theorem solution (P : ComplexArchParam) :
    ∃ D : ArchDatumC P, ∃ g : GL (Fin 2) ℂ, D.W g ≠ 0 :=
  TateComplex.Datum.exists_archDatumC_WmemC P

#print axioms solution

end S_LanglandsTunnell_Converse_exists_archDatumC_W_ne_zero
end P2MW
export P2MW.S_LanglandsTunnell_Converse_exists_archDatumC_W_ne_zero (solution)
