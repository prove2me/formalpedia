-- Prove2me | solution 1 for LanglandsTunnell.Converse.PrincipalFamily.exists_Wmem_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/2a7cb82d-e6fa-503f-9b71-f295510ee651

import Definitions.Def_LanglandsTunnell_ArchCasimirCompanion
import Definitions.Def_LanglandsTunnell_Converse_ExplicitWhittakerFunctions
import Definitions.Def_LanglandsTunnell_ArchPlace
import Theorems.Thm_LanglandsTunnell_TateLocal_localZeta_fourier_mul_symm
import Theorems.Thm_LanglandsTunnell_TateLocal_realZeta_eq_localZeta
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_real_eq_nnnorm
import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_Converse_PrincipalFamily_exists_Wmem_ne_zero

set_option autoImplicit false

open Complex MeasureTheory FourierTransform

noncomputable section

namespace TateReal

private def sgnPow (a : ZMod 2) (w : ℝ) : ℂ := if a = 0 then 1 else ((SignType.sign w : ℝ) : ℂ)

private def tateZeta (f : ℝ → ℂ) (a : ZMod 2) (s : ℂ) : ℂ :=
  ∫ w : ℝ, f w * sgnPow a w * ((|w| : ℝ) : ℂ) ^ (s - 1)

private def gaussPoly (p : Polynomial ℂ) (α : ℝ) (β : ℂ) (w : ℝ) : ℂ :=
  p.eval (w : ℂ) * cexp (-Real.pi * α * (w : ℂ) ^ 2 + 2 * Real.pi * β * w)

private def IsGaussPoly (f : ℝ → ℂ) : Prop := ∃ (p : Polynomial ℂ) (α : ℝ) (β : ℂ), 0 < α ∧ f = gaussPoly p α β

private def gaussStd (a : ZMod 2) (w : ℝ) : ℂ :=
  (if a = 0 then 1 else ((w : ℝ) : ℂ)) * (Real.exp (-Real.pi * w ^ 2) : ℂ)

private def sh (a : ZMod 2) : ℂ := if a = 0 then 0 else 1

private theorem fourier_gauss_even :
    (𝓕 fun x : ℝ => cexp (-Real.pi * x ^ 2)) = fun t : ℝ => cexp (-Real.pi * t ^ 2) := by
  have h := fourier_gaussian_pi (b := (1 : ℂ)) (by simp)
  simpa using h

private theorem fourier_const_mul (c : ℂ) (f : ℝ → ℂ) :
    (𝓕 fun x : ℝ => c * f x) = fun w : ℝ => c * 𝓕 f w := by
  funext w
  simp only [Real.fourier_real_eq_integral_exp_smul, smul_eq_mul]
  have hv : ∀ v : ℝ, cexp (((-2 * Real.pi * v * w : ℝ) : ℂ) * I) * (c * f v)
      = c * (cexp (((-2 * Real.pi * v * w : ℝ) : ℂ) * I) * f v) := fun v => by ring
  simp_rw [hv]
  exact MeasureTheory.integral_const_mul _ _

private theorem fourier_gauss_odd :
    (𝓕 fun x : ℝ => (x : ℂ) * cexp (-Real.pi * x ^ 2)) = fun t : ℝ => -I * t * cexp (-Real.pi * t ^ 2) := by
  have hint : MeasureTheory.Integrable (fun x : ℝ => cexp (-Real.pi * x ^ 2)) :=
    integrable_cexp_neg_mul_sq (by simp [Real.pi_pos])
  have hint' : MeasureTheory.Integrable (fun x : ℝ => x • cexp (-Real.pi * x ^ 2)) := by
    simpa [smul_eq_mul] using integrable_mul_cexp_neg_mul_sq (b := (Real.pi : ℂ)) (by simp [Real.pi_pos])
  have hd := Real.deriv_fourier hint hint'
  rw [fourier_gauss_even] at hd
  have hlin : (fun x : ℝ => (-2 * Real.pi * I * x) • cexp (-Real.pi * x ^ 2))
      = fun x : ℝ => (-2 * Real.pi * I) * ((x : ℂ) * cexp (-Real.pi * x ^ 2)) := by
    funext x; simp only [smul_eq_mul]; ring
  rw [hlin, fourier_const_mul] at hd
  have hderiv : deriv (fun t : ℝ => cexp (-Real.pi * t ^ 2))
      = fun t : ℝ => (-2 * Real.pi * t) * cexp (-Real.pi * t ^ 2) := by
    funext t
    have : HasDerivAt (fun t : ℝ => cexp (-Real.pi * (t : ℂ) ^ 2))
        (cexp (-Real.pi * (t : ℂ) ^ 2) * (-Real.pi * (2 * (t : ℂ)))) t := by
      have h1 : HasDerivAt (fun t : ℝ => (-Real.pi * (t : ℂ) ^ 2)) (-Real.pi * (2 * (t : ℂ))) t := by
        have := ((hasDerivAt_id t).ofReal_comp).pow 2
        simpa using this.const_mul (-(Real.pi : ℂ))
      exact h1.cexp
    rw [this.deriv]; ring
  rw [hderiv] at hd
  funext t
  have ht := congrFun hd t
  set F := 𝓕 (fun x : ℝ => (x : ℂ) * cexp (-Real.pi * x ^ 2)) t with hF
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have key : (-2 * (Real.pi : ℂ)) * (F - (-I * t * cexp (-Real.pi * t ^ 2))) = 0 := by
    linear_combination I * ht + (-2 * (Real.pi : ℂ) * F) * Complex.I_sq
  have h2 : (-2 * (Real.pi : ℂ)) ≠ 0 := by simp
  exact sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_left h2)

private theorem integral_comp_abs' (f : ℝ → ℂ) : ∫ x : ℝ, f |x| = 2 * ∫ x in Set.Ioi (0 : ℝ), f x := by
  have eq : ∫ x in Set.Ioi (0 : ℝ), f |x| = ∫ x in Set.Ioi (0 : ℝ), f x := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun _ hx => ?_)
    rw [abs_eq_self.mpr (le_of_lt (by exact hx))]
  by_cases hf : IntegrableOn (fun x => f |x|) (Set.Ioi 0)
  · have int_Iic : IntegrableOn (fun x => f |x|) (Set.Iic 0) := by
      rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
      let m : MeasurableEmbedding fun x : ℝ => -x := (Homeomorph.neg ℝ).measurableEmbedding
      rw [m.integrableOn_map_iff]
      simp_rw [Function.comp_def, abs_neg, Set.neg_preimage, Set.neg_Iic, neg_zero]
      exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hf
    calc
      _ = (∫ x in Set.Iic 0, f |x|) + ∫ x in Set.Ioi 0, f |x| := by
        rw [← setIntegral_union (Set.Iic_disjoint_Ioi le_rfl) measurableSet_Ioi int_Iic hf,
          Set.Iic_union_Ioi, Measure.restrict_univ]
      _ = 2 * ∫ x in Set.Ioi 0, f x := by
        rw [two_mul, eq]
        congr! 1
        rw [← neg_zero, ← integral_comp_neg_Iic, neg_zero]
        refine setIntegral_congr_fun measurableSet_Iic (fun _ hx => ?_)
        rw [abs_eq_neg_self.mpr (by exact hx)]
  · have : ¬ Integrable (fun x => f |x|) := fun h => hf h.integrableOn
    rw [integral_undef this, integral_undef (fun h => hf ?_), mul_zero]

    exact (integrableOn_congr_fun (fun x hx => by rw [abs_eq_self.mpr (le_of_lt (by exact hx))])
      measurableSet_Ioi).mpr h

private theorem integral_gauss_abs_cpow {z : ℂ} (hz : 0 < z.re) :
    ∫ w : ℝ, (Real.exp (-Real.pi * w ^ 2) : ℂ) * ((|w| : ℝ) : ℂ) ^ (z - 1) = Gammaℝ z := by

  have h1 := integral_comp_abs' (fun r : ℝ => (Real.exp (-Real.pi * r ^ 2) : ℂ) * ((r : ℝ) : ℂ) ^ (z - 1))
  simp only [sq_abs] at h1
  rw [h1]

  have h2 : (∫ r in Set.Ioi (0 : ℝ), (Real.exp (-Real.pi * r ^ 2) : ℂ) * ((r : ℝ) : ℂ) ^ (z - 1))
      = mellin (fun r : ℝ => (Real.exp (-Real.pi * r ^ (2 : ℝ)) : ℂ)) z := by
    unfold mellin
    refine setIntegral_congr_fun measurableSet_Ioi (fun r _ => ?_)
    simp only [smul_eq_mul]
    rw [Real.rpow_two]; ring
  have hcomp := mellin_comp_rpow (fun t : ℝ => (Real.exp (-Real.pi * t) : ℂ)) z (2 : ℝ)
  rw [h2, hcomp]

  have h3 : mellin (fun t : ℝ => (Real.exp (-Real.pi * t) : ℂ)) (z / 2) = Gammaℝ z := by
    have h := hasSum_mellin_pi_mul_sq (ι := Unit) (a := fun _ => (1 : ℂ)) (r := fun _ => (1 : ℝ))
      (F := fun t : ℝ => (Real.exp (-Real.pi * t) : ℂ)) hz ?_ ?_
    · simpa using h.tsum_eq.symm
    · intro t _; simp
    · exact (hasSum_fintype _).summable
  rw [show (z / ((2 : ℝ) : ℂ)) = z / 2 by norm_num, h3]

  have key : (2 : ℂ) * (((|(2 : ℝ)|⁻¹ : ℝ) : ℂ) * Gammaℝ z) = Gammaℝ z := by
    rw [abs_two]; push_cast; ring
  convert key using 2 <;> first | rfl | exact Complex.real_smul

private theorem tateZeta_gaussStd (a : ZMod 2) {s : ℂ} (hs : 0 < s.re) :
    tateZeta (gaussStd a) a s = Gammaℝ (s + sh a) := by
  unfold tateZeta gaussStd sgnPow sh
  by_cases ha : a = 0
  · simp only [ha, if_true, one_mul, mul_one, add_zero, add_zero]
    rw [← integral_gauss_abs_cpow hs]
  · simp only [ha, if_false]
    have hs' : 0 < (s + 1).re := by simp; linarith
    rw [← integral_gauss_abs_cpow hs']
    congr 1; funext w
    rcases eq_or_ne w 0 with rfl | hw
    · have hs0 : s ≠ 0 := fun h => by simp [h] at hs
      simp [hs0]
    · have habs : ((|w| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (abs_pos.mpr hw).ne'
      have hws : ((w : ℝ) : ℂ) * (((SignType.sign w : ℝ)) : ℂ) = ((|w| : ℝ) : ℂ) := by
        rcases hw.lt_or_gt with h | h
        · simp [sign_neg h, abs_of_neg h]
        · simp [sign_pos h, abs_of_pos h]
      rw [show s + 1 - 1 = 1 + (s - 1) by ring, Complex.cpow_add _ _ habs, Complex.cpow_one, ← hws]
      ring

private theorem fourier_gaussStd (a : ZMod 2) :
    𝓕 (gaussStd a) = fun w : ℝ => (-I) ^ (if a = 0 then 0 else 1 : ℕ) * gaussStd a w := by
  unfold gaussStd
  by_cases ha : a = 0
  · simp only [ha, if_true, one_mul, pow_zero]
    have hfun : (fun w : ℝ => (Real.exp (-Real.pi * w ^ 2) : ℂ)) = fun x : ℝ => cexp (-Real.pi * x ^ 2) := by
      funext x; push_cast; rfl
    rw [hfun, fourier_gauss_even]
  · simp only [ha, if_false, pow_one]
    have hfun : (fun w : ℝ => ((w : ℝ) : ℂ) * (Real.exp (-Real.pi * w ^ 2) : ℂ))
        = fun x : ℝ => (x : ℂ) * cexp (-Real.pi * x ^ 2) := by
      funext x; push_cast; rfl
    rw [hfun, fourier_gauss_odd]
    funext t; push_cast; ring

private theorem tateZeta_const_mul (c : ℂ) (f : ℝ → ℂ) (a : ZMod 2) (s : ℂ) :
    tateZeta (fun w => c * f w) a s = c * tateZeta f a s := by
  unfold tateZeta
  have h : (∫ w : ℝ, c * (f w * sgnPow a w * ((|w| : ℝ) : ℂ) ^ (s - 1)))
      = c * ∫ w : ℝ, f w * sgnPow a w * ((|w| : ℝ) : ℂ) ^ (s - 1) := integral_const_mul _ _
  rw [← h]
  congr 1; funext w; ring

private theorem gaussStd_isGaussPoly (a : ZMod 2) : IsGaussPoly (gaussStd a) := by
  refine ⟨if a = 0 then 1 else Polynomial.X, 1, 0, one_pos, ?_⟩
  funext w
  unfold gaussStd gaussPoly
  by_cases ha : a = 0 <;> simp [ha, Complex.ofReal_exp]

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

private theorem isGaussPoly_gaussPoly (p : Polynomial ℂ) {α : ℝ} (hα : 0 < α) (β : ℂ)
    : IsGaussPoly (gaussPoly p α β) :=
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

private theorem IsGaussPoly.fourier {f : ℝ → ℂ} (hf : IsGaussPoly f) : IsGaussPoly (𝓕 f) := by
  obtain ⟨p, α, β, hα, rfl⟩ := hf
  obtain ⟨q, hq⟩ := fourier_gaussPoly p hα β
  exact ⟨q, 1 / α, -I * β / α, by positivity, hq⟩

end TateReal

namespace TateReal

open LanglandsTunnell.TateLocal LanglandsTunnell.ArchPlace
open scoped ENNReal

private theorem charExt_realCharFun (a : ZMod 2) {w : ℝ} (hw : w ≠ 0) : charExt (realCharFun 0 a) w = sgnPow a w := by
  rw [charExt_of_ne_zero _ hw]
  have hval : (realCharFun 0 a (Units.mk0 w hw) : ℂ) = (((w : ℝ) : ℂ) / ((‖w‖ : ℝ) : ℂ)) ^ (a.val : ℕ) := by
    simp [realCharFun, realSign]
  rw [hval]
  unfold sgnPow
  by_cases ha : a = 0
  · simp [ha]
  · have ha1 : a.val = 1 := by
      fin_cases a
      · exact absurd rfl ha
      · rfl
    rw [ha1, pow_one, if_neg ha, Real.norm_eq_abs]
    rcases hw.lt_or_gt with h | h
    · rw [abs_of_neg h, sign_neg h]; push_cast
      rw [div_neg, div_self (by exact_mod_cast hw)]; simp
    · rw [abs_of_pos h, sign_pos h]
      rw [div_self (by exact_mod_cast hw)]; simp

private theorem tateZeta_eq_realZeta (f : ℝ → ℂ) (a : ZMod 2) (s : ℂ) :
    tateZeta f a s = realZeta volume f (realCharFun 0 a) s := by
  unfold tateZeta realZeta
  refine integral_congr_ae ?_
  filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ))] with w hw
  have hw0 : w ≠ 0 := hw
  rw [charExt_realCharFun a hw0, Real.norm_eq_abs]

private theorem realCharFun_zero_inv (a : ZMod 2) : (realCharFun 0 a)⁻¹ = realCharFun 0 a := by
  refine MonoidHom.ext fun x => ?_
  rw [MonoidHom.inv_apply]
  refine inv_eq_of_mul_eq_one_left (Units.ext ?_)
  have hx : (x : ℝ) ≠ 0 := x.ne_zero
  have hval : (realCharFun 0 a x : ℂ) = (((x : ℝ) : ℂ) / ((‖(x : ℝ)‖ : ℝ) : ℂ)) ^ (a.val : ℕ) := by
    simp [realCharFun, realSign]
  rw [Units.val_mul, hval, Units.val_one, ← mul_pow]
  have hsq : ((x : ℝ) : ℂ) / ((‖(x : ℝ)‖ : ℝ) : ℂ) * (((x : ℝ) : ℂ) / ((‖(x : ℝ)‖ : ℝ) : ℂ)) = 1 := by
    rw [Real.norm_eq_abs, div_mul_div_comm, ← Complex.ofReal_mul, ← Complex.ofReal_mul, abs_mul_abs_self]
    exact div_self (by exact_mod_cast mul_ne_zero hx hx)
  rw [hsq, one_pow]

private theorem tateFourier_psiReal (f : ℝ → ℂ) : tateFourier psiReal volume f = 𝓕 f := by
  funext y
  rw [Real.fourier_eq']
  unfold tateFourier
  congr 1; funext x
  have hin : (inner ℝ x y : ℝ) = y * x := rfl
  rw [psiReal_apply, smul_eq_mul, hin, mul_comm (f x)]
  congr 2
  push_cast
  ring

private theorem norm_psiReal (t : ℝ) : ‖(psiReal t : ℂ)‖ = 1 := by
  rw [psiReal_apply, Complex.norm_exp]
  simp

private theorem aemeasurable_modulus_inv :
    AEMeasurable (fun x : ℝ => (modulus x)⁻¹) ((volume : Measure ℝ).restrict {0}ᶜ) := by
  simp_rw [modulus_real_eq_nnnorm]
  exact measurable_nnnorm.inv.aemeasurable

private theorem integrable_kernel {f g : ℝ → ℂ} (hf : IsGaussPoly f) (hg : IsGaussPoly g) (x : ℝ) :
    Integrable (fun p : ℝ × ℝ => f p.1 * g p.2 * (psiReal (p.1 * p.2 * x) : ℂ))
      ((volume : Measure ℝ).prod volume) := by
  refine (hf.integrable.mul_prod hg.integrable).mul_bdd (c := 1) ?_ (Filter.Eventually.of_forall fun p => ?_)
  · have hc : Continuous fun p : ℝ × ℝ => (psiReal (p.1 * p.2 * x) : ℂ) := by
      simp_rw [psiReal_apply]
      exact Complex.continuous_exp.comp (by fun_prop)
    exact hc.aestronglyMeasurable
  · exact (norm_psiReal _).le

private theorem IsGaussPoly.continuous {f : ℝ → ℂ} (hf : IsGaussPoly f) : Continuous f := by
  obtain ⟨p, α, β, -, rfl⟩ := hf
  unfold gaussPoly
  exact (p.continuous.comp Complex.continuous_ofReal).mul (Complex.continuous_exp.comp
    ((continuous_const.mul (Complex.continuous_ofReal.pow 2)).add (continuous_const.mul Complex.continuous_ofReal)))

private theorem IsGaussPoly.comp_mul_left {f : ℝ → ℂ} (hf : IsGaussPoly f) {c : ℝ} (hc : c ≠ 0) :
    IsGaussPoly fun x : ℝ => f (c * x) := by
  obtain ⟨p, α, β, hα, rfl⟩ := hf
  refine ⟨p.comp (Polynomial.C (c : ℂ) * Polynomial.X), α * c ^ 2, β * c, by positivity, ?_⟩
  funext x
  simp only [gaussPoly, Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  push_cast
  ring_nf

private theorem charExt_eq_ite (a : ZMod 2) : charExt (realCharFun 0 a)
    = fun x : ℝ => if x = 0 then 0 else sgnPow a x := by
  funext x
  split_ifs with hx
  · subst hx; simp [charExt]
  · exact charExt_realCharFun a hx

private theorem measurable_charExt (a : ZMod 2) : Measurable (charExt (realCharFun 0 a)) := by
  rw [charExt_eq_ite]
  exact Measurable.ite (by simp) measurable_const (measurable_sgnPow a)

private theorem norm_charExt_of_ne_zero (a : ZMod 2) {x : ℝ} (hx : x ≠ 0) : ‖charExt (realCharFun 0 a) x‖ = 1 := by
  rw [charExt_realCharFun a hx, norm_sgnPow a hx]

private theorem modulus_real_cast (y : ℝ) : ((modulus y : ℝ) : ℂ) = ((|y| : ℝ) : ℂ) := by
  rw [modulus_real_eq_nnnorm, coe_nnnorm, Real.norm_eq_abs]

private theorem measurable_modulus_inv_ennreal : Measurable fun x : ℝ => ((modulus x : ℝ≥0∞))⁻¹ := by
  simp_rw [modulus_real_eq_nnnorm]
  exact measurable_nnnorm.coe_nnreal_ennreal.inv

private theorem ae_modulus_inv_lt_top : ∀ᵐ x ∂(volume : Measure ℝ), ((modulus x : ℝ≥0∞))⁻¹ < ⊤ := by
  filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ))] with x hx
  have hx0 : x ≠ 0 := hx
  rw [modulus_real_eq_nnnorm]
  exact ENNReal.inv_lt_top.mpr (by simp [hx0])

private theorem modulus_inv_toReal (x : ℝ) : (((modulus x : ℝ≥0∞))⁻¹).toReal = |x|⁻¹ := by
  rw [modulus_real_eq_nnnorm, ENNReal.toReal_inv]; simp [Real.norm_eq_abs]

private theorem mulMeasure_volume_eq :
    mulMeasure (volume : Measure ℝ) = (volume : Measure ℝ).withDensity fun x => ((modulus x : ℝ≥0∞))⁻¹ := by
  unfold mulMeasure
  have hres : (volume : Measure ℝ).restrict ({0}ᶜ : Set ℝ) = volume :=
    Measure.restrict_eq_self_of_ae_mem (compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ)))
  rw [hres]

private theorem integrable_mulMeasure_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {h : ℝ → E} :
    Integrable h (mulMeasure (volume : Measure ℝ)) ↔ Integrable (fun x : ℝ => |x|⁻¹ • h x) volume := by
  rw [mulMeasure_volume_eq, integrable_withDensity_iff_integrable_smul' measurable_modulus_inv_ennreal
    ae_modulus_inv_lt_top]
  simp_rw [modulus_inv_toReal]

private theorem integrable_mulMeasure_iff_complex {h : ℝ → ℂ} :
    Integrable h (mulMeasure (volume : Measure ℝ)) ↔ Integrable (fun x : ℝ => ((|x|⁻¹ : ℝ) : ℂ) * h x) volume :=
  integrable_mulMeasure_iff

private theorem sfinite_mulMeasure : SFinite (mulMeasure (volume : Measure ℝ)) := by
  rw [mulMeasure_volume_eq]; infer_instance

private theorem integral_mulMeasure (h : ℝ → ℝ) :
    ∫ x, h x ∂(mulMeasure (volume : Measure ℝ)) = ∫ x : ℝ, |x|⁻¹ * h x := by
  rw [mulMeasure_volume_eq, integral_withDensity_eq_integral_toReal_smul measurable_modulus_inv_ennreal
    ae_modulus_inv_lt_top]
  simp_rw [modulus_inv_toReal, smul_eq_mul]

private theorem integrable_slice {F : ℝ → ℂ} (hF : IsGaussPoly F) (a : ZMod 2) {s : ℂ} (hs₁ : s.re < 1) (c : ℂ) {y : ℝ}
    (hy : y ≠ 0) :
    Integrable (fun x : ℝ => c * F (y * x) * (charExt (realCharFun 0 a) x * ((|x| : ℝ) : ℂ) ^ (1 - s)))
      (mulMeasure (volume : Measure ℝ)) := by
  rw [integrable_mulMeasure_iff_complex]
  have h1s : 0 < (1 - s).re := by simp; linarith
  have hint := ((hF.comp_mul_left hy).integrable_tate a h1s).const_mul c
  refine hint.congr ?_
  filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ))] with x hx
  have hx0 : x ≠ 0 := hx
  have habs : ((|x| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (abs_pos.mpr hx0).ne'
  rw [charExt_realCharFun a hx0, Complex.cpow_sub _ _ habs, Complex.cpow_one]
  push_cast
  field_simp

private theorem integral_norm_slice (u F : ℝ → ℂ) (a : ZMod 2) (s : ℂ) {y : ℝ} (hy : y ≠ 0) :
    (∫ x, ‖u y * ((|y| : ℝ) : ℂ) * F (y * x) * (charExt (realCharFun 0 a) x * ((|x| : ℝ) : ℂ) ^ (1 - s))‖
        ∂(mulMeasure (volume : Measure ℝ)))
      = ‖u y‖ * |y| ^ s.re * ∫ t : ℝ, ‖F t‖ * |t| ^ (-s.re) := by
  have hyabs : 0 < |y| := abs_pos.mpr hy
  rw [integral_mulMeasure]

  have hpt : (fun x : ℝ => |x|⁻¹ *
      ‖u y * ((|y| : ℝ) : ℂ) * F (y * x) * (charExt (realCharFun 0 a) x * ((|x| : ℝ) : ℂ) ^ (1 - s))‖)
      =ᵐ[volume] fun x : ℝ => (‖u y‖ * |y| * |y| ^ s.re) * (‖F (y * x)‖ * |y * x| ^ (-s.re)) := by
    filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ))] with x hx
    have hx0 : x ≠ 0 := hx
    have hxabs : 0 < |x| := abs_pos.mpr hx0
    rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_charExt_of_ne_zero a hx0, one_mul,
      norm_cpow_eq_rpow_re_of_pos hxabs, Complex.norm_real, Real.norm_eq_abs, abs_abs, Complex.sub_re,
      Complex.one_re, abs_mul, Real.mul_rpow hyabs.le hxabs.le, Real.rpow_neg hyabs.le, Real.rpow_neg hxabs.le,
      show (1 : ℝ) - s.re = (1 - s.re - 1) + 1 by ring, Real.rpow_add_one hxabs.ne',
      show (1 : ℝ) - s.re - 1 = -s.re by ring, Real.rpow_neg hxabs.le]
    field_simp
  rw [integral_congr_ae hpt]
  have hconst : (∫ x : ℝ, (‖u y‖ * |y| * |y| ^ s.re) * (‖F (y * x)‖ * |y * x| ^ (-s.re)))
      = (‖u y‖ * |y| * |y| ^ s.re) * ∫ x : ℝ, ‖F (y * x)‖ * |y * x| ^ (-s.re) := integral_const_mul _ _
  rw [hconst, Measure.integral_comp_mul_left (fun t : ℝ => ‖F t‖ * |t| ^ (-s.re)) y, abs_inv, smul_eq_mul]
  field_simp

private theorem integrable_swap {u v : ℝ → ℂ} (hu : IsGaussPoly u) (hv : IsGaussPoly v) (a : ZMod 2) {s : ℂ}
    (hs₀ : 0 < s.re) (hs₁ : s.re < 1) :
    Integrable (Function.uncurry fun y x : ℝ =>
        u y * ((modulus y : ℝ) : ℂ) * tateFourier psiReal volume v (y * x) *
          (charExt (realCharFun 0 a)⁻¹ x * ((modulus x : ℝ) : ℂ) ^ (1 - s)))
      ((mulMeasure (volume : Measure ℝ)).prod (mulMeasure volume)) := by
  rw [tateFourier_psiReal, realCharFun_zero_inv]
  simp_rw [modulus_real_cast]
  obtain ⟨F, hFdef⟩ : ∃ F : ℝ → ℂ, F = 𝓕 v := ⟨_, rfl⟩
  rw [← hFdef]
  have hF : IsGaussPoly F := hFdef ▸ hv.fourier
  have hmeas : AEStronglyMeasurable (Function.uncurry fun y x : ℝ =>
      u y * ((|y| : ℝ) : ℂ) * F (y * x) * (charExt (realCharFun 0 a) x * ((|x| : ℝ) : ℂ) ^ (1 - s)))
      ((mulMeasure (volume : Measure ℝ)).prod (mulMeasure volume)) := by
    refine Measurable.aestronglyMeasurable ?_
    show Measurable fun p : ℝ × ℝ =>
      u p.1 * ((|p.1| : ℝ) : ℂ) * F (p.1 * p.2) * (charExt (realCharFun 0 a) p.2 * ((|p.2| : ℝ) : ℂ) ^ (1 - s))
    exact (((hu.continuous.measurable.comp measurable_fst).mul
        (Complex.measurable_ofReal.comp (measurable_abs.comp measurable_fst))).mul
        (hF.continuous.measurable.comp (measurable_fst.mul measurable_snd))).mul
      (((measurable_charExt a).comp measurable_snd).mul
        ((Complex.measurable_ofReal.comp (measurable_abs.comp measurable_snd)).pow_const _))
  haveI := sfinite_mulMeasure
  rw [integrable_prod_iff hmeas]
  simp only [Function.uncurry_apply_pair]
  refine ⟨Filter.Eventually.of_forall fun y => ?_, ?_⟩
  ·
    by_cases hy : y = 0
    · subst hy; simp only [abs_zero, Complex.ofReal_zero, mul_zero, zero_mul]; exact integrable_zero _ _ _
    · exact integrable_slice hF a hs₁ (u y * ((|y| : ℝ) : ℂ)) hy
  ·
    have hval : (fun y : ℝ => ∫ x, ‖u y * ((|y| : ℝ) : ℂ) * F (y * x) *
          (charExt (realCharFun 0 a) x * ((|x| : ℝ) : ℂ) ^ (1 - s))‖ ∂(mulMeasure (volume : Measure ℝ)))
        = fun y : ℝ => (∫ t : ℝ, ‖F t‖ * |t| ^ (-s.re)) * (‖u y‖ * |y| ^ s.re) := by
      funext y
      by_cases hy : y = 0
      · subst hy
        simp [Real.zero_rpow hs₀.ne']
      · rw [integral_norm_slice u F a s hy]; ring
    rw [hval, integrable_mulMeasure_iff]
    have hint := ((hu.integrable_tate 0 hs₀).norm).const_mul (∫ t : ℝ, ‖F t‖ * |t| ^ (-s.re))
    refine hint.congr ?_
    filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ))] with y hy
    have hy0 : y ≠ 0 := hy
    have hyabs : 0 < |y| := abs_pos.mpr hy0
    rw [norm_mul, norm_mul, norm_sgnPow 0 hy0, mul_one, norm_cpow_eq_rpow_re_of_pos hyabs, Complex.sub_re,
      Complex.one_re, Real.rpow_sub_one hyabs.ne', smul_eq_mul]
    field_simp

private theorem tate_symmetry {f g : ℝ → ℂ} (hf : IsGaussPoly f) (hg : IsGaussPoly g) (a : ZMod 2) {s : ℂ}
    (hs₀ : 0 < s.re) (hs₁ : s.re < 1) :
    tateZeta f a s * tateZeta (𝓕 g) a (1 - s) = tateZeta (𝓕 f) a (1 - s) * tateZeta g a s := by
  have hsym := localZeta_fourier_mul_symm (volume : Measure ℝ) psiReal f g (realCharFun 0 a) s
    aemeasurable_modulus_inv (integrable_swap hg hf a hs₀ hs₁) (integrable_swap hf hg a hs₀ hs₁)
    (fun x _ => integrable_kernel hf hg x)
  rw [← realZeta_eq_localZeta, ← realZeta_eq_localZeta, ← realZeta_eq_localZeta, ← realZeta_eq_localZeta,
    realCharFun_zero_inv, tateFourier_psiReal, tateFourier_psiReal, ← tateZeta_eq_realZeta, ← tateZeta_eq_realZeta,
    ← tateZeta_eq_realZeta, ← tateZeta_eq_realZeta] at hsym
  linear_combination (-1 : ℂ) * hsym

private theorem strip_functional_equation {f : ℝ → ℂ} (hf : IsGaussPoly f) (a : ZMod 2) {s : ℂ}
    (hs₀ : 0 < s.re) (hs₁ : s.re < 1) :
    tateZeta (𝓕 f) a (1 - s) * Gammaℝ (s + sh a)
      = (-I) ^ (if a = 0 then 0 else 1 : ℕ) * Gammaℝ (1 - s + sh a) * tateZeta f a s := by
  have hsym := tate_symmetry hf (gaussStd_isGaussPoly a) a hs₀ hs₁
  have h1s : 0 < (1 - s).re := by simp; linarith
  rw [fourier_gaussStd a, tateZeta_const_mul, tateZeta_gaussStd a h1s, tateZeta_gaussStd a hs₀] at hsym
  linear_combination (-1 : ℂ) * hsym

namespace W3

private def gexp (α₁ α₂ γr γi : ℝ) (β₁ β₂ : ℂ) (x t : ℝ) : ℂ :=
  (-Real.pi * α₁ * (x : ℂ) ^ 2 + 2 * Real.pi * (β₁ + (γr + γi * I) * t) * x)
    + (-Real.pi * α₂ * (t : ℂ) ^ 2 + 2 * Real.pi * β₂ * t)

private def _root_.TateReal.W3.gen (α₁ α₂ γr γi : ℝ) (β₁ β₂ : ℂ) (x t : ℝ) : ℂ := cexp (gexp α₁ α₂ γr γi β₁ β₂ x t)

p2m_export "TateReal.W3" "gen"
private structure Adm (α₁ α₂ γr γi : ℝ) : Prop where
  h₁ : 0 < α₁
  h₂ : 0 < α₂
  hγ : γr * γi = 0
  hpd : γr ^ 2 < α₁ * α₂

private theorem Adm.swap {α₁ α₂ γr γi : ℝ} (h : Adm α₁ α₂ γr γi) : Adm α₂ α₁ γr γi :=
  ⟨h.h₂, h.h₁, h.hγ, by rw [mul_comm]; exact h.hpd⟩

private inductive Cls : (ℝ → ℝ → ℂ) → Prop
  | gen {α₁ α₂ γr γi : ℝ} (β₁ β₂ : ℂ) (h : Adm α₁ α₂ γr γi) : Cls (gen α₁ α₂ γr γi β₁ β₂)
  | smul (c : ℂ) {Ψ : ℝ → ℝ → ℂ} (hΨ : Cls Ψ) : Cls (fun x t => c * Ψ x t)
  | add {Ψ Φ : ℝ → ℝ → ℂ} (hΨ : Cls Ψ) (hΦ : Cls Φ) : Cls (fun x t => Ψ x t + Φ x t)
  | mulX {Ψ : ℝ → ℝ → ℂ} (hΨ : Cls Ψ) : Cls (fun x t => (x : ℂ) * Ψ x t)
  | mulT {Ψ : ℝ → ℝ → ℂ} (hΨ : Cls Ψ) : Cls (fun x t => (t : ℂ) * Ψ x t)

private theorem Cls.congr {Ψ Φ : ℝ → ℝ → ℂ} (h : Cls Ψ) (e : Ψ = Φ) : Cls Φ := by
  subst e
  exact h

private theorem gen_swap (α₁ α₂ γr γi : ℝ) (β₁ β₂ : ℂ) :
    (fun x t => gen α₁ α₂ γr γi β₁ β₂ t x) = gen α₂ α₁ γr γi β₂ β₁ := by
  funext x t
  simp only [gen, gexp]
  congr 1
  ring

private theorem Cls.swap {Ψ : ℝ → ℝ → ℂ} (h : Cls Ψ) : Cls (fun x t => Ψ t x) := by
  induction h with
  | @gen α₁ α₂ γr γi β₁ β₂ hadm => exact (Cls.gen β₂ β₁ hadm.swap).congr (gen_swap α₁ α₂ γr γi β₁ β₂).symm
  | smul c _ ih => exact ih.smul c
  | add _ _ ih₁ ih₂ => exact ih₁.add ih₂
  | mulX _ ih => exact ih.mulT
  | mulT _ ih => exact ih.mulX

private theorem continuous_gen (α₁ α₂ γr γi : ℝ) (β₁ β₂ : ℂ) :
    Continuous (fun p : ℝ × ℝ => gen α₁ α₂ γr γi β₁ β₂ p.1 p.2) := by
  unfold gen gexp
  fun_prop

private theorem Cls.continuous {Ψ : ℝ → ℝ → ℂ} (h : Cls Ψ) : Continuous (fun p : ℝ × ℝ => Ψ p.1 p.2) := by
  induction h with
  | gen β₁ β₂ _ => exact continuous_gen _ _ _ _ β₁ β₂
  | smul c _ ih => exact continuous_const.mul ih
  | add _ _ ih₁ ih₂ => exact ih₁.add ih₂
  | mulX _ ih => exact (Complex.continuous_ofReal.comp continuous_fst).mul ih
  | mulT _ ih => exact (Complex.continuous_ofReal.comp continuous_snd).mul ih

private theorem gexp_re (α₁ α₂ γr γi : ℝ) (β₁ β₂ : ℂ) (x t : ℝ) :
    (gexp α₁ α₂ γr γi β₁ β₂ x t).re
      = -Real.pi * (α₁ * x ^ 2 + α₂ * t ^ 2 - 2 * γr * x * t) + 2 * Real.pi * (β₁.re * x + β₂.re * t) := by
  simp only [gexp, Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.add_im, Complex.re_ofNat,
    Complex.im_ofNat]
  simp only [← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_im]
  ring

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

private theorem norm_gen_le {α₁ α₂ γr γi : ℝ} (β₁ β₂ : ℂ) (h : Adm α₁ α₂ γr γi) :
    ∃ (K δ : ℝ), 0 < δ ∧ ∀ x t : ℝ, ‖gen α₁ α₂ γr γi β₁ β₂ x t‖ ≤ Real.exp K * Real.exp (-δ * (x ^ 2 + t ^ 2)) := by
  obtain ⟨lam, hlam, hQ⟩ := exists_pd_lower h.h₁ h.h₂ h.hpd
  refine ⟨2 * Real.pi * (β₁.re ^ 2 + β₂.re ^ 2) / lam, Real.pi * lam / 2, by positivity, fun x t => ?_⟩
  rw [gen, Complex.norm_exp, ← Real.exp_add, gexp_re]
  apply Real.exp_le_exp.mpr
  have amgm : ∀ b y : ℝ, b * y ≤ lam / 4 * y ^ 2 + b ^ 2 / lam := fun b y => by
    rw [← sub_nonneg]
    have e : lam / 4 * y ^ 2 + b ^ 2 / lam - b * y = (lam * y - 2 * b) ^ 2 / (4 * lam) := by
      field_simp
      ring
    rw [e]
    positivity
  have hx := amgm β₁.re x
  have ht := amgm β₂.re t
  have hQ' := hQ x t
  have hpi := Real.pi_pos
  have e : 2 * Real.pi * (β₁.re ^ 2 + β₂.re ^ 2) / lam
      = 2 * Real.pi * (β₁.re ^ 2 / lam + β₂.re ^ 2 / lam) := by field_simp
  rw [e]
  nlinarith [mul_le_mul_of_nonneg_left hx (by positivity : (0:ℝ) ≤ 2 * Real.pi),
    mul_le_mul_of_nonneg_left ht (by positivity : (0:ℝ) ≤ 2 * Real.pi),
    mul_le_mul_of_nonneg_left hQ' hpi.le]

private theorem Cls.bound {Ψ : ℝ → ℝ → ℂ} (h : Cls Ψ) :
    ∃ (C : ℝ) (N : ℕ) (δ : ℝ), 0 ≤ C ∧ 0 < δ ∧
      ∀ x t : ℝ, ‖Ψ x t‖ ≤ C * (1 + |x| + |t|) ^ N * Real.exp (-δ * (x ^ 2 + t ^ 2)) := by
  induction h with
  | gen β₁ β₂ hadm =>
    obtain ⟨K, δ, hδ, hb⟩ := norm_gen_le β₁ β₂ hadm
    exact ⟨Real.exp K, 0, δ, (Real.exp_pos _).le, hδ, fun x t => by simpa using hb x t⟩
  | smul c _ ih =>
    obtain ⟨C, N, δ, hC, hδ, hb⟩ := ih
    refine ⟨‖c‖ * C, N, δ, by positivity, hδ, fun x t => ?_⟩
    rw [norm_mul]
    calc ‖c‖ * ‖_‖ ≤ ‖c‖ * (C * (1 + |x| + |t|) ^ N * Real.exp (-δ * (x ^ 2 + t ^ 2))) :=
          mul_le_mul_of_nonneg_left (hb x t) (norm_nonneg _)
      _ = ‖c‖ * C * (1 + |x| + |t|) ^ N * Real.exp (-δ * (x ^ 2 + t ^ 2)) := by ring
  | add _ _ ih₁ ih₂ =>
    obtain ⟨C₁, N₁, δ₁, hC₁, hδ₁, hb₁⟩ := ih₁
    obtain ⟨C₂, N₂, δ₂, hC₂, hδ₂, hb₂⟩ := ih₂
    refine ⟨C₁ + C₂, max N₁ N₂, min δ₁ δ₂, by positivity, lt_min hδ₁ hδ₂, fun x t => ?_⟩
    have hB : 1 ≤ 1 + |x| + |t| := by linarith [abs_nonneg x, abs_nonneg t]
    have hr : 0 ≤ x ^ 2 + t ^ 2 := by positivity
    have hp₁ : (1 + |x| + |t|) ^ N₁ ≤ (1 + |x| + |t|) ^ max N₁ N₂ :=
      pow_le_pow_right₀ hB (le_max_left _ _)
    have hp₂ : (1 + |x| + |t|) ^ N₂ ≤ (1 + |x| + |t|) ^ max N₁ N₂ :=
      pow_le_pow_right₀ hB (le_max_right _ _)
    have he₁ : Real.exp (-δ₁ * (x ^ 2 + t ^ 2)) ≤ Real.exp (-min δ₁ δ₂ * (x ^ 2 + t ^ 2)) :=
      Real.exp_le_exp.mpr (by nlinarith [min_le_left δ₁ δ₂])
    have he₂ : Real.exp (-δ₂ * (x ^ 2 + t ^ 2)) ≤ Real.exp (-min δ₁ δ₂ * (x ^ 2 + t ^ 2)) :=
      Real.exp_le_exp.mpr (by nlinarith [min_le_right δ₁ δ₂])
    calc ‖_ + _‖ ≤ ‖_‖ + ‖_‖ := norm_add_le _ _
      _ ≤ C₁ * (1 + |x| + |t|) ^ N₁ * Real.exp (-δ₁ * (x ^ 2 + t ^ 2))
          + C₂ * (1 + |x| + |t|) ^ N₂ * Real.exp (-δ₂ * (x ^ 2 + t ^ 2)) := add_le_add (hb₁ x t) (hb₂ x t)
      _ ≤ C₁ * (1 + |x| + |t|) ^ max N₁ N₂ * Real.exp (-min δ₁ δ₂ * (x ^ 2 + t ^ 2))
          + C₂ * (1 + |x| + |t|) ^ max N₁ N₂ * Real.exp (-min δ₁ δ₂ * (x ^ 2 + t ^ 2)) := by gcongr
      _ = (C₁ + C₂) * (1 + |x| + |t|) ^ max N₁ N₂ * Real.exp (-min δ₁ δ₂ * (x ^ 2 + t ^ 2)) := by ring
  | mulX _ ih =>
    obtain ⟨C, N, δ, hC, hδ, hb⟩ := ih
    refine ⟨C, N + 1, δ, hC, hδ, fun x t => ?_⟩
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, pow_succ]
    have hxB : |x| ≤ 1 + |x| + |t| := by linarith [abs_nonneg t]
    calc |x| * ‖_‖ ≤ |x| * (C * (1 + |x| + |t|) ^ N * Real.exp (-δ * (x ^ 2 + t ^ 2))) :=
          mul_le_mul_of_nonneg_left (hb x t) (abs_nonneg _)
      _ ≤ (1 + |x| + |t|) * (C * (1 + |x| + |t|) ^ N * Real.exp (-δ * (x ^ 2 + t ^ 2))) := by gcongr
      _ = C * ((1 + |x| + |t|) ^ N * (1 + |x| + |t|)) * Real.exp (-δ * (x ^ 2 + t ^ 2)) := by ring
  | mulT _ ih =>
    obtain ⟨C, N, δ, hC, hδ, hb⟩ := ih
    refine ⟨C, N + 1, δ, hC, hδ, fun x t => ?_⟩
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, pow_succ]
    have htB : |t| ≤ 1 + |x| + |t| := by linarith [abs_nonneg x]
    calc |t| * ‖_‖ ≤ |t| * (C * (1 + |x| + |t|) ^ N * Real.exp (-δ * (x ^ 2 + t ^ 2))) :=
          mul_le_mul_of_nonneg_left (hb x t) (abs_nonneg _)
      _ ≤ (1 + |x| + |t|) * (C * (1 + |x| + |t|) ^ N * Real.exp (-δ * (x ^ 2 + t ^ 2))) := by gcongr
      _ = C * ((1 + |x| + |t|) ^ N * (1 + |x| + |t|)) * Real.exp (-δ * (x ^ 2 + t ^ 2)) := by ring

private inductive InSpan : (ℝ → ℂ) → Prop
  | mem {f : ℝ → ℂ} (hf : IsGaussPoly f) : InSpan f
  | smul (c : ℂ) {f : ℝ → ℂ} (hf : InSpan f) : InSpan (fun w => c * f w)
  | add {f g : ℝ → ℂ} (hf : InSpan f) (hg : InSpan g) : InSpan (fun w => f w + g w)

private theorem InSpan.congr {f g : ℝ → ℂ} (h : InSpan f) (e : f = g) : InSpan g := by
  subst e
  exact h

private theorem gaussPoly_X_mul_fun (p : Polynomial ℂ) (α : ℝ) (β : ℂ) :
    (fun w : ℝ => (w : ℂ) * gaussPoly p α β w) = gaussPoly (Polynomial.X * p) α β := by
  funext w
  simp only [gaussPoly, Polynomial.eval_mul, Polynomial.eval_X]
  ring

private theorem InSpan.mulW {f : ℝ → ℂ} (h : InSpan f) : InSpan (fun w => (w : ℂ) * f w) := by
  induction h with
  | mem hf =>
    obtain ⟨p, α, β, hα, rfl⟩ := hf
    exact (InSpan.mem ⟨Polynomial.X * p, α, β, hα, rfl⟩ : InSpan (gaussPoly (Polynomial.X * p) α β)).congr
      (gaussPoly_X_mul_fun p α β).symm
  | smul c _ ih =>
    refine ih.smul c |>.congr ?_
    funext w; ring
  | add _ _ ih₁ ih₂ =>
    refine ih₁.add ih₂ |>.congr ?_
    funext w; ring

private theorem gen_slice (α₁ α₂ γr γi : ℝ) (β₁ β₂ : ℂ) (t : ℝ) :
    (fun x => gen α₁ α₂ γr γi β₁ β₂ x t)
      = fun x => cexp (-Real.pi * α₂ * (t : ℂ) ^ 2 + 2 * Real.pi * β₂ * t)
          * gaussPoly (Polynomial.C 1) α₁ (β₁ + (γr + γi * I) * t) x := by
  funext x
  simp only [gen, gexp, gaussPoly, Polynomial.eval_C, one_mul, Complex.exp_add]
  ring

private theorem Cls.sliceX {Ψ : ℝ → ℝ → ℂ} (h : Cls Ψ) (t : ℝ) : InSpan (fun x => Ψ x t) := by
  induction h with
  | gen β₁ β₂ hadm =>
    rw [gen_slice]
    exact InSpan.smul _ (InSpan.mem ⟨Polynomial.C 1, _, _, hadm.h₁, rfl⟩)
  | smul c _ ih => exact ih.smul c
  | add _ _ ih₁ ih₂ => exact ih₁.add ih₂
  | mulX _ ih => exact ih.mulW
  | mulT _ ih => exact ih.smul (t : ℂ)

private theorem Cls.sliceT {Ψ : ℝ → ℝ → ℂ} (h : Cls Ψ) (x : ℝ) : InSpan (fun t => Ψ x t) := h.swap.sliceX x

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

private theorem InSpan.integrable {f : ℝ → ℂ} (h : InSpan f) : Integrable f := by
  induction h with
  | mem hf => exact hf.integrable
  | smul c _ ih => exact ih.const_mul c
  | add _ _ ih₁ ih₂ => exact ih₁.add ih₂

private theorem Cls.integrable_sliceX {Ψ : ℝ → ℝ → ℂ} (h : Cls Ψ) (t : ℝ) : Integrable (fun x => Ψ x t) :=
  (h.sliceX t).integrable

private theorem Cls.integrable_sliceT {Ψ : ℝ → ℝ → ℂ} (h : Cls Ψ) (x : ℝ) : Integrable (fun t => Ψ x t) :=
  (h.sliceT x).integrable

private def _root_.TateReal.W3.F₁ (Ψ : ℝ → ℝ → ℂ) (ξ t : ℝ) : ℂ := 𝓕 (fun x => Ψ x t) ξ

p2m_export "TateReal.W3" "F₁"
private def _root_.TateReal.W3.F₂ (Ψ : ℝ → ℝ → ℂ) (x τ : ℝ) : ℂ := 𝓕 (fun t => Ψ x t) τ

p2m_export "TateReal.W3" "F₂"
private theorem F₂_eq_swap_F₁_swap (Ψ : ℝ → ℝ → ℂ) : F₂ Ψ = fun x τ => F₁ (fun a b => Ψ b a) τ x := rfl

private theorem F₁_smul (c : ℂ) (Ψ : ℝ → ℝ → ℂ) : F₁ (fun x t => c * Ψ x t) = fun ξ t => c * F₁ Ψ ξ t := by
  funext ξ t
  simp only [F₁]
  rw [fourier_const_mul]

private theorem F₁_mulT (Ψ : ℝ → ℝ → ℂ) : F₁ (fun x t => (t : ℂ) * Ψ x t) = fun (ξ t : ℝ) => (t : ℂ) * F₁ Ψ ξ t := by
  funext ξ t
  simp only [F₁]
  rw [fourier_const_mul]

private theorem F₁_add {Ψ Φ : ℝ → ℝ → ℂ} (hΨ : Cls Ψ) (hΦ : Cls Φ) :
    F₁ (fun x t => Ψ x t + Φ x t) = fun ξ t => F₁ Ψ ξ t + F₁ Φ ξ t := by
  funext ξ t
  simp only [F₁]
  have e : (fun x => Ψ x t + Φ x t) = (fun x => Ψ x t) + (fun x => Φ x t) := rfl
  rw [e, fourier_add' (hΨ.integrable_sliceX t) (hΦ.integrable_sliceX t)]
  rfl

private theorem hasDerivAt_ofReal' (x : ℝ) : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := by
  first | simpa using Complex.ofRealCLM.hasDerivAt (x := x) | (have h' := Complex.ofRealCLM.hasDerivAt (x := x); simp at h'; exact h') | exact Complex.ofRealCLM.hasDerivAt (x := x)

private theorem hasDerivAt_gexp (α₁ α₂ γr γi : ℝ) (β₁ β₂ : ℂ) (x t : ℝ) :
    HasDerivAt (fun x : ℝ => gexp α₁ α₂ γr γi β₁ β₂ x t)
      (-Real.pi * α₁ * (2 * (x : ℂ)) + 2 * Real.pi * (β₁ + (γr + γi * I) * t)) x := by
  have hx := hasDerivAt_ofReal' x
  have h1 := (hx.pow 2).const_mul (-Real.pi * α₁ : ℂ)
  have h2 := hx.const_mul (2 * Real.pi * (β₁ + (γr + γi * I) * t) : ℂ)
  have h := (h1.add h2).add_const (-Real.pi * α₂ * (t : ℂ) ^ 2 + 2 * Real.pi * β₂ * t)
  convert h using 1 <;> first | rfl | (simp; done) | simp

private theorem deriv_gen (α₁ α₂ γr γi : ℝ) (β₁ β₂ : ℂ) (x t : ℝ) :
    deriv (fun x : ℝ => gen α₁ α₂ γr γi β₁ β₂ x t) x
      = -(2 * Real.pi * α₁) * ((x : ℂ) * gen α₁ α₂ γr γi β₁ β₂ x t)
        + ((2 * Real.pi * β₁) * gen α₁ α₂ γr γi β₁ β₂ x t
          + (2 * Real.pi * (γr + γi * I)) * ((t : ℂ) * gen α₁ α₂ γr γi β₁ β₂ x t)) := by
  have h := (hasDerivAt_gexp α₁ α₂ γr γi β₁ β₂ x t).cexp
  rw [show (fun x : ℝ => gen α₁ α₂ γr γi β₁ β₂ x t) = fun x : ℝ => cexp (gexp α₁ α₂ γr γi β₁ β₂ x t) from rfl,
    h.deriv, gen]
  ring

private theorem Cls.differentiableX {Ψ : ℝ → ℝ → ℂ} (h : Cls Ψ) (t : ℝ) : Differentiable ℝ (fun x => Ψ x t) := by
  induction h with
  | gen β₁ β₂ _ => exact fun x => (hasDerivAt_gexp _ _ _ _ β₁ β₂ x t).cexp.differentiableAt
  | smul c _ ih => exact ih.const_mul c
  | add _ _ ih₁ ih₂ => exact ih₁.add ih₂
  | mulX _ ih => exact fun x => ((hasDerivAt_ofReal' x).mul (ih x).hasDerivAt).differentiableAt
  | mulT _ ih => exact ih.const_mul _

private theorem Cls.derivX {Ψ : ℝ → ℝ → ℂ} (h : Cls Ψ) : Cls (fun x t => deriv (fun x => Ψ x t) x) := by
  induction h with
  | @gen α₁ α₂ γr γi β₁ β₂ hadm =>
    have key : (fun x t => deriv (fun x => W3.gen α₁ α₂ γr γi β₁ β₂ x t) x)
        = fun (x t : ℝ) => -(2 * Real.pi * α₁) * ((x : ℂ) * W3.gen α₁ α₂ γr γi β₁ β₂ x t)
          + ((2 * Real.pi * β₁) * W3.gen α₁ α₂ γr γi β₁ β₂ x t
            + (2 * Real.pi * (γr + γi * I)) * ((t : ℂ) * W3.gen α₁ α₂ γr γi β₁ β₂ x t)) := by
      funext x t; exact deriv_gen α₁ α₂ γr γi β₁ β₂ x t
    rw [key]
    exact ((Cls.gen β₁ β₂ hadm).mulX.smul _).add
      (((Cls.gen β₁ β₂ hadm).smul _).add ((Cls.gen β₁ β₂ hadm).mulT.smul _))
  | @smul c Ψ hΨ ih =>
    have key : (fun x t => deriv (fun x => c * Ψ x t) x) = fun x t => c * deriv (fun x => Ψ x t) x := by
      funext x t
      exact deriv_const_mul c (hΨ.differentiableX t x)
    rw [key]
    exact ih.smul c
  | @add Ψ Φ hΨ hΦ ih₁ ih₂ =>
    have key : (fun x t => deriv (fun x => Ψ x t + Φ x t) x)
        = fun x t => deriv (fun x => Ψ x t) x + deriv (fun x => Φ x t) x := by
      funext x t
      exact deriv_add (hΨ.differentiableX t x) (hΦ.differentiableX t x)
    rw [key]
    exact ih₁.add ih₂
  | @mulX Ψ hΨ ih =>
    have key : (fun x t => deriv (fun x : ℝ => (x : ℂ) * Ψ x t) x)
        = fun (x t : ℝ) => Ψ x t + (x : ℂ) * deriv (fun x => Ψ x t) x := by
      funext x t
      have hd : HasDerivAt (fun y : ℝ => (y : ℂ) * Ψ y t) (1 * Ψ x t + (x : ℂ) * deriv (fun x => Ψ x t) x) x :=
        (hasDerivAt_ofReal' x).mul (hΨ.differentiableX t x).hasDerivAt
      rw [hd.deriv, one_mul]
    rw [key]
    exact hΨ.add ih.mulX
  | @mulT Ψ hΨ ih =>
    have key : (fun (x t : ℝ) => deriv (fun x => (t : ℂ) * Ψ x t) x)
        = fun (x t : ℝ) => (t : ℂ) * deriv (fun x => Ψ x t) x := by
      funext x t
      exact deriv_const_mul _ (hΨ.differentiableX t x)
    rw [key]
    exact ih.mulT

private theorem gen_slice' (α₁ α₂ γr γi : ℝ) (β₁ β₂ : ℂ) (t : ℝ) :
    (fun x => gen α₁ α₂ γr γi β₁ β₂ x t)
      = fun x : ℝ => cexp (-Real.pi * α₂ * (t : ℂ) ^ 2 + 2 * Real.pi * β₂ * t)
          * cexp (-Real.pi * (α₁ : ℂ) * (x : ℂ) ^ 2 + 2 * Real.pi * (β₁ + (γr + γi * I) * t) * x) := by
  funext x
  simp only [gen, gexp, Complex.exp_add]
  ring

private theorem Adm.transformed {α₁ α₂ γr γi : ℝ} (h : Adm α₁ α₂ γr γi) :
    Adm (1 / α₁) (α₂ - (γr ^ 2 - γi ^ 2) / α₁) (γi / α₁) (-γr / α₁) := by
  have h₁ := h.h₁
  have hpd := h.hpd
  refine ⟨by positivity, ?_, ?_, ?_⟩
  · rw [sub_pos, div_lt_iff₀ h₁]
    nlinarith [sq_nonneg γi]
  · have := h.hγ
    field_simp
    linear_combination -this
  · have key : (1 / α₁) * (α₂ - (γr ^ 2 - γi ^ 2) / α₁) - (γi / α₁) ^ 2 = (α₁ * α₂ - γr ^ 2) / α₁ ^ 2 := by
      field_simp
      ring
    rw [← sub_pos, key]
    exact div_pos (by linarith) (by positivity)

private theorem F₁_gen {α₁ α₂ γr γi : ℝ} (β₁ β₂ : ℂ) (h : Adm α₁ α₂ γr γi) :
    F₁ (gen α₁ α₂ γr γi β₁ β₂)
      = fun ξ t => (1 / (α₁ : ℂ) ^ (1 / 2 : ℂ) * cexp (Real.pi * β₁ ^ 2 / α₁))
          * gen (1 / α₁) (α₂ - (γr ^ 2 - γi ^ 2) / α₁) (γi / α₁) (-γr / α₁) (-I * β₁ / α₁)
              (β₂ + β₁ * (γr + γi * I) / α₁) ξ t := by
  funext ξ t
  have hα : (0 : ℝ) < (α₁ : ℂ).re := by simpa using h.h₁
  have hα0 : (α₁ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h.h₁.ne'
  simp only [F₁]
  rw [gen_slice', fourier_const_mul, fourier_gaussian_pi' hα (β₁ + (γr + γi * I) * t)]

  have hexp : (-Real.pi * α₂ * (t : ℂ) ^ 2 + 2 * Real.pi * β₂ * t)
        + (-Real.pi / α₁ * ((ξ : ℂ) + I * (β₁ + (γr + γi * I) * t)) ^ 2)
      = Real.pi * β₁ ^ 2 / α₁
        + gexp (1 / α₁) (α₂ - (γr ^ 2 - γi ^ 2) / α₁) (γi / α₁) (-γr / α₁) (-I * β₁ / α₁)
            (β₂ + β₁ * (γr + γi * I) / α₁) ξ t := by
    have hγ : (γr : ℂ) * γi = 0 := by exact_mod_cast h.hγ
    simp only [gexp]
    push_cast
    field_simp
    linear_combination (-2 * (t : ℂ) * ξ * γi - 2 * (t : ℂ) * I * β₁ * γi - 2 * (t : ℂ) * β₁ * γr
      - (t : ℂ) ^ 2 * γr ^ 2 - (t : ℂ) ^ 2 * γi ^ 2 * (I ^ 2 - 1) - β₁ ^ 2) * Complex.I_sq
      + (-2 * (t : ℂ) ^ 2 * I ^ 3) * hγ
  have hE := congrArg cexp hexp
  rw [Complex.exp_add (-Real.pi * α₂ * (t : ℂ) ^ 2 + 2 * Real.pi * β₂ * t)
      (-Real.pi / α₁ * ((ξ : ℂ) + I * (β₁ + (γr + γi * I) * t)) ^ 2),
    Complex.exp_add (Real.pi * β₁ ^ 2 / α₁)] at hE
  simp only [gen]
  linear_combination (1 / (α₁ : ℂ) ^ (1 / 2 : ℂ)) * hE

private theorem Cls.F₁ {Ψ : ℝ → ℝ → ℂ} (h : Cls Ψ) : Cls (W3.F₁ Ψ) := by
  induction h with
  | @gen α₁ α₂ γr γi β₁ β₂ hadm =>
    rw [F₁_gen β₁ β₂ hadm]
    exact (Cls.gen _ _ hadm.transformed).smul _
  | @smul c Ψ _ ih =>
    rw [F₁_smul]
    exact ih.smul c
  | @add Ψ Φ hΨ hΦ ih₁ ih₂ =>
    rw [F₁_add hΨ hΦ]
    exact ih₁.add ih₂
  | @mulX Ψ hΨ ih =>
    have key : W3.F₁ (fun x t => (x : ℂ) * Ψ x t)
        = fun ξ t => (-(2 * Real.pi * I))⁻¹ * deriv (fun ξ => W3.F₁ Ψ ξ t) ξ := by
      funext ξ t
      have hf := hΨ.integrable_sliceX t
      have hf' : Integrable (fun x : ℝ => x • Ψ x t) := by
        simpa [Complex.real_smul] using hΨ.mulX.integrable_sliceX t
      have hd := Real.deriv_fourier hf hf'
      have hlin : (fun x : ℝ => (-2 * Real.pi * I * x) • Ψ x t)
          = fun x : ℝ => (-(2 * Real.pi * I)) * ((x : ℂ) * Ψ x t) := by
        funext x; simp only [smul_eq_mul]; ring
      rw [hlin, fourier_const_mul] at hd
      have hne : (-(2 * Real.pi * I)) ≠ 0 := by simp [Real.pi_ne_zero]
      have e : (fun ξ => W3.F₁ Ψ ξ t) = 𝓕 (fun x => Ψ x t) := rfl
      rw [e, hd]
      simp only [W3.F₁]
      field_simp
    rw [key]
    exact ih.derivX.smul _
  | @mulT Ψ _ ih =>
    rw [F₁_mulT]
    exact ih.mulT

private theorem Cls.F₂ {Ψ : ℝ → ℝ → ℂ} (h : Cls Ψ) : Cls (W3.F₂ Ψ) := by
  rw [F₂_eq_swap_F₁_swap]
  exact h.swap.F₁.swap

end W3

namespace W3

private theorem measurable_sgnPow₂ (a : ZMod 2) : Measurable (sgnPow a) := by
  have hcast : Monotone fun t : SignType => (t : ℝ) := by
    intro x y hxy
    cases x <;> cases y <;> simp_all
  unfold sgnPow
  by_cases ha : a = 0
  · simp only [ha, if_true]; exact measurable_const
  · simp only [ha, if_false]
    exact Complex.measurable_ofReal.comp (hcast.comp SignType.sign.monotone).measurable

private def ker (a : ZMod 2) (w : ℂ) (x : ℝ) : ℂ := sgnPow a x * ((|x| : ℝ) : ℂ) ^ (w - 1)

private theorem measurable_ker (a : ZMod 2) (w : ℂ) : Measurable (ker a w) :=
  (measurable_sgnPow₂ a).mul ((Complex.measurable_ofReal.comp measurable_abs).pow_const _)

private theorem tateZeta_eq_integral_ker (f : ℝ → ℂ) (a : ZMod 2) (s : ℂ) :
    tateZeta f a s = ∫ x, f x * ker a s x := by
  unfold tateZeta ker
  congr 1
  funext x
  ring

private theorem norm_sgnPow_le (a : ZMod 2) (x : ℝ) : ‖sgnPow a x‖ ≤ 1 := by
  unfold sgnPow
  split_ifs
  · simp
  · rw [Complex.norm_real, Real.norm_eq_abs]
    rcases lt_trichotomy x 0 with h | h | h <;> simp [h]

private def prof (σlo σhi : ℝ) (x : ℝ) : ℝ := |x| ^ (σlo - 1) + |x| ^ (σhi - 1) + |x| ^ (0 : ℝ)

private theorem prof_nonneg (σlo σhi x : ℝ) : 0 ≤ prof σlo σhi x := by
  unfold prof; positivity

private theorem norm_ker_le (a : ZMod 2) {w : ℂ} {σlo σhi : ℝ} (hlo : σlo ≤ w.re) (hhi : w.re ≤ σhi) (x : ℝ) :
    ‖ker a w x‖ ≤ prof σlo σhi x := by
  unfold ker prof
  rcases eq_or_ne x 0 with rfl | hx
  · have h1 : ‖((|(0 : ℝ)| : ℝ) : ℂ) ^ (w - 1)‖ ≤ 1 := by
      simp only [abs_zero, Complex.ofReal_zero]
      by_cases hw : w - 1 = 0
      · simp [hw]
      · simp [Complex.zero_cpow hw]
    have h0 : (0 : ℝ) ≤ |(0 : ℝ)| ^ (σlo - 1) + |(0 : ℝ)| ^ (σhi - 1) := by positivity
    calc ‖sgnPow a 0 * ((|(0 : ℝ)| : ℝ) : ℂ) ^ (w - 1)‖ = ‖sgnPow a 0‖ * ‖((|(0 : ℝ)| : ℝ) : ℂ) ^ (w - 1)‖ :=
          norm_mul _ _
      _ ≤ 1 * 1 := mul_le_mul (norm_sgnPow_le a 0) h1 (norm_nonneg _) zero_le_one
      _ = |(0 : ℝ)| ^ (0 : ℝ) := by simp
      _ ≤ _ := by linarith
  · have hpos : 0 < |x| := abs_pos.mpr hx
    rw [norm_mul, norm_sgnPow a hx, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos hpos, Complex.sub_re,
      Complex.one_re]
    have h0 : (0 : ℝ) ≤ |x| ^ (0 : ℝ) := by positivity
    rcases le_or_gt |x| 1 with h1 | h1
    · have : |x| ^ (w.re - 1) ≤ |x| ^ (σlo - 1) :=
        Real.rpow_le_rpow_of_exponent_ge hpos h1 (by linarith)
      have h2 : (0 : ℝ) ≤ |x| ^ (σhi - 1) := by positivity
      exact this.trans ((le_add_of_nonneg_right h2).trans (le_add_of_nonneg_right h0))
    · have : |x| ^ (w.re - 1) ≤ |x| ^ (σhi - 1) :=
        Real.rpow_le_rpow_of_exponent_le h1.le (by linarith)
      have h2 : (0 : ℝ) ≤ |x| ^ (σlo - 1) := by positivity
      exact this.trans ((le_add_of_nonneg_left h2).trans (le_add_of_nonneg_right h0))

private theorem integrable_prof_mul_exp {σlo σhi δ : ℝ} (hlo : 0 < σlo) (hhi : 0 < σhi) (hδ : 0 < δ) :
    Integrable (fun x : ℝ => prof σlo σhi x * Real.exp (-δ * x ^ 2)) := by
  have h1 := integrable_abs_rpow_mul_exp hδ (t := σlo - 1) (by linarith)
  have h2 := integrable_abs_rpow_mul_exp hδ (t := σhi - 1) (by linarith)
  have h3 := integrable_abs_rpow_mul_exp hδ (t := 0) (by norm_num)
  have := (h1.add h2).add h3
  refine this.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [prof, Pi.add_apply]
  ring

private theorem Cls.bound' {Ψ : ℝ → ℝ → ℂ} (h : Cls Ψ) :
    ∃ (C δ : ℝ), 0 ≤ C ∧ 0 < δ ∧ ∀ x t : ℝ, ‖Ψ x t‖ ≤ C * (Real.exp (-δ * x ^ 2) * Real.exp (-δ * t ^ 2)) := by
  obtain ⟨C, N, δ, hC, hδ, hb⟩ := h.bound
  refine ⟨C * (N.factorial * Real.exp (1 + 1 / δ)), δ / 2, by positivity, by positivity, fun x t => ?_⟩

  have hpoly : (1 + |x| + |t|) ^ N ≤ N.factorial * Real.exp (1 + |x| + |t|) := by
    have h := Real.pow_div_factorial_le_exp (x := 1 + |x| + |t|) (by positivity) N
    have hf : (0 : ℝ) < N.factorial := by exact_mod_cast N.factorial_pos
    rwa [div_le_iff₀ hf, mul_comm] at h
  have hamx : |x| ≤ δ / 2 * x ^ 2 + 1 / (2 * δ) := by
    have h0 : 0 ≤ (δ * |x| - 1) ^ 2 := sq_nonneg _
    have hx2 : |x| ^ 2 = x ^ 2 := sq_abs x
    rw [← sub_nonneg]
    have e : δ / 2 * x ^ 2 + 1 / (2 * δ) - |x| = (δ * |x| - 1) ^ 2 / (2 * δ) := by
      field_simp
      rw [← hx2]
      ring
    rw [e]
    positivity
  have hamt : |t| ≤ δ / 2 * t ^ 2 + 1 / (2 * δ) := by
    have h0 : 0 ≤ (δ * |t| - 1) ^ 2 := sq_nonneg _
    have ht2 : |t| ^ 2 = t ^ 2 := sq_abs t
    rw [← sub_nonneg]
    have e : δ / 2 * t ^ 2 + 1 / (2 * δ) - |t| = (δ * |t| - 1) ^ 2 / (2 * δ) := by
      field_simp
      rw [← ht2]
      ring
    rw [e]
    positivity
  have hexp : Real.exp (1 + |x| + |t|) * Real.exp (-δ * (x ^ 2 + t ^ 2))
      ≤ Real.exp (1 + 1 / δ) * (Real.exp (-(δ / 2) * x ^ 2) * Real.exp (-(δ / 2) * t ^ 2)) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have e : 1 / δ = 1 / (2 * δ) + 1 / (2 * δ) := by field_simp; ring
    nlinarith [hamx, hamt, e]
  calc ‖Ψ x t‖ ≤ C * (1 + |x| + |t|) ^ N * Real.exp (-δ * (x ^ 2 + t ^ 2)) := hb x t
    _ ≤ C * (N.factorial * Real.exp (1 + |x| + |t|)) * Real.exp (-δ * (x ^ 2 + t ^ 2)) := by gcongr
    _ = C * N.factorial * (Real.exp (1 + |x| + |t|) * Real.exp (-δ * (x ^ 2 + t ^ 2))) := by ring
    _ ≤ C * N.factorial * (Real.exp (1 + 1 / δ) * (Real.exp (-(δ / 2) * x ^ 2) * Real.exp (-(δ / 2) * t ^ 2))) := by
        gcongr
    _ = C * (N.factorial * Real.exp (1 + 1 / δ)) * (Real.exp (-(δ / 2) * x ^ 2) * Real.exp (-(δ / 2) * t ^ 2)) := by
        ring

private def zint (Ψ : ℝ → ℝ → ℂ) (a₁ a₂ : ZMod 2) (w₁ w₂ : ℂ) (p : ℝ × ℝ) : ℂ :=
  Ψ p.1 p.2 * ker a₁ w₁ p.1 * ker a₂ w₂ p.2

private def Z (Ψ : ℝ → ℝ → ℂ) (a₁ a₂ : ZMod 2) (w₁ w₂ : ℂ) : ℂ := ∫ p : ℝ × ℝ, zint Ψ a₁ a₂ w₁ w₂ p

private theorem Cls.aestronglyMeasurable_zint {Ψ : ℝ → ℝ → ℂ} (h : Cls Ψ) (a₁ a₂ : ZMod 2) (w₁ w₂ : ℂ) :
    AEStronglyMeasurable (zint Ψ a₁ a₂ w₁ w₂) ((volume : Measure ℝ).prod volume) :=
  ((h.continuous.measurable.mul ((measurable_ker a₁ w₁).comp measurable_fst)).mul
    ((measurable_ker a₂ w₂).comp measurable_snd)).aestronglyMeasurable

private theorem Cls.exists_dominator {Ψ : ℝ → ℝ → ℂ} (h : Cls Ψ) {σlo σhi : ℝ} (hlo : 0 < σlo) (hhi : 0 < σhi) :
    ∃ D : ℝ → ℝ, Integrable D ∧ (∀ x, 0 ≤ D x) ∧
      ∀ (a₁ a₂ : ZMod 2) (w₁ w₂ : ℂ), σlo ≤ w₁.re → w₁.re ≤ σhi → σlo ≤ w₂.re → w₂.re ≤ σhi →
        ∀ p : ℝ × ℝ, ‖zint Ψ a₁ a₂ w₁ w₂ p‖ ≤ D p.1 * D p.2 := by
  obtain ⟨C, δ, hC, hδ, hb⟩ := h.bound'
  refine ⟨fun x => Real.sqrt C * (prof σlo σhi x * Real.exp (-δ * x ^ 2)),
    (integrable_prof_mul_exp hlo hhi hδ).const_mul _,
    fun x => mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg (prof_nonneg _ _ _) (Real.exp_pos _).le),
    fun a₁ a₂ w₁ w₂ h1 h2 h3 h4 p => ?_⟩
  simp only [zint]
  rw [norm_mul, norm_mul]
  have hk₁ := norm_ker_le a₁ h1 h2 p.1
  have hk₂ := norm_ker_le a₂ h3 h4 p.2
  have hsq : Real.sqrt C * Real.sqrt C = C := Real.mul_self_sqrt hC
  have hE : (0 : ℝ) ≤ C * (Real.exp (-δ * p.1 ^ 2) * Real.exp (-δ * p.2 ^ 2)) := by positivity
  calc ‖Ψ p.1 p.2‖ * ‖ker a₁ w₁ p.1‖ * ‖ker a₂ w₂ p.2‖
      ≤ (C * (Real.exp (-δ * p.1 ^ 2) * Real.exp (-δ * p.2 ^ 2))) * prof σlo σhi p.1 * prof σlo σhi p.2 :=
        mul_le_mul (mul_le_mul (hb p.1 p.2) hk₁ (norm_nonneg _) hE) hk₂ (norm_nonneg _)
          (mul_nonneg hE (prof_nonneg _ _ _))
    _ = Real.sqrt C * (prof σlo σhi p.1 * Real.exp (-δ * p.1 ^ 2))
          * (Real.sqrt C * (prof σlo σhi p.2 * Real.exp (-δ * p.2 ^ 2))) := by
        linear_combination (-(Real.exp (-δ * p.1 ^ 2) * Real.exp (-δ * p.2 ^ 2) * prof σlo σhi p.1
          * prof σlo σhi p.2)) * hsq

private theorem Cls.integrable_zint {Ψ : ℝ → ℝ → ℂ} (h : Cls Ψ) (a₁ a₂ : ZMod 2) {w₁ w₂ : ℂ} (h₁ : 0 < w₁.re)
    (h₂ : 0 < w₂.re) : Integrable (zint Ψ a₁ a₂ w₁ w₂) ((volume : Measure ℝ).prod volume) := by
  obtain ⟨D, hD, hD0, hbound⟩ := h.exists_dominator (σlo := min w₁.re w₂.re) (σhi := max w₁.re w₂.re)
    (lt_min h₁ h₂) (lt_max_of_lt_left h₁)
  refine (hD.mul_prod hD).mono' (h.aestronglyMeasurable_zint a₁ a₂ w₁ w₂) (Filter.Eventually.of_forall fun p => ?_)
  exact hbound a₁ a₂ w₁ w₂ (min_le_left _ _) (le_max_left _ _) (min_le_right _ _) (le_max_right _ _) p

private theorem Z_swap (Ψ : ℝ → ℝ → ℂ) (a₁ a₂ : ZMod 2) (w₁ w₂ : ℂ) :
    Z (fun x t => Ψ t x) a₂ a₁ w₂ w₁ = Z Ψ a₁ a₂ w₁ w₂ := by
  unfold Z
  rw [Measure.volume_eq_prod, ← integral_prod_swap (zint Ψ a₁ a₂ w₁ w₂)]
  congr 1
  funext p
  simp only [zint, Prod.fst_swap, Prod.snd_swap]
  ring

private theorem Cls.Z_eq_iterated {Ψ : ℝ → ℝ → ℂ} (h : Cls Ψ) (a₁ a₂ : ZMod 2) {w₁ w₂ : ℂ} (h₁ : 0 < w₁.re)
    (h₂ : 0 < w₂.re) :
    Z Ψ a₁ a₂ w₁ w₂ = ∫ t : ℝ, tateZeta (fun x => Ψ x t) a₁ w₁ * ker a₂ w₂ t := by
  unfold Z
  rw [Measure.volume_eq_prod, integral_prod_symm _ (h.integrable_zint a₁ a₂ h₁ h₂)]
  congr 1
  funext t
  simp only [zint]
  rw [tateZeta_eq_integral_ker]
  exact integral_mul_const (ker a₂ w₂ t) (fun x => Ψ x t * ker a₁ w₁ x)

private theorem Cls.exists_Z_bound {Ψ : ℝ → ℝ → ℂ} (h : Cls Ψ) {σlo σhi : ℝ} (hlo : 0 < σlo) (hhi : 0 < σhi) :
    ∃ M : ℝ, ∀ (a₁ a₂ : ZMod 2) (w₁ w₂ : ℂ), σlo ≤ w₁.re → w₁.re ≤ σhi → σlo ≤ w₂.re → w₂.re ≤ σhi →
      ‖Z Ψ a₁ a₂ w₁ w₂‖ ≤ M := by
  obtain ⟨D, hD, _, hbound⟩ := h.exists_dominator hlo hhi
  refine ⟨∫ p : ℝ × ℝ, D p.1 * D p.2 ∂((volume : Measure ℝ).prod volume), fun a₁ a₂ w₁ w₂ h1 h2 h3 h4 => ?_⟩
  unfold Z
  rw [Measure.volume_eq_prod]
  exact norm_integral_le_of_norm_le (hD.mul_prod hD)
    (Filter.Eventually.of_forall fun p => hbound a₁ a₂ w₁ w₂ h1 h2 h3 h4 p)

end W3

namespace W3

private def epsW (b : ZMod 2) : ℂ := (-I) ^ (if b = 0 then 0 else 1 : ℕ)

private theorem epsW_ne_zero (b : ZMod 2) : epsW b ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr I_ne_zero)

private theorem cint_mul_const (f : ℝ → ℂ) (r : ℂ) : ∫ x, f x * r = (∫ x, f x) * r := integral_mul_const r f

private theorem cint_const_mul (r : ℂ) (f : ℝ → ℂ) : ∫ x, r * f x = r * ∫ x, f x := integral_const_mul r f

private theorem InSpan.integrable_tate {f : ℝ → ℂ} (h : InSpan f) (a : ZMod 2) {s : ℂ} (hs : 0 < s.re) :
    Integrable (fun w : ℝ => f w * sgnPow a w * ((|w| : ℝ) : ℂ) ^ (s - 1)) := by
  induction h with
  | mem hf => exact hf.integrable_tate a hs
  | smul c _ ih =>
    refine (ih.const_mul c).congr (Filter.Eventually.of_forall fun w => ?_)
    simp only
    ring
  | add _ _ ih₁ ih₂ =>
    refine (ih₁.add ih₂).congr (Filter.Eventually.of_forall fun w => ?_)
    simp only [Pi.add_apply]
    ring

private theorem InSpan.fourier {f : ℝ → ℂ} (h : InSpan f) : InSpan (𝓕 f) := by
  induction h with
  | mem hf => exact InSpan.mem hf.fourier
  | smul c _ ih =>
    rw [fourier_const_mul]
    exact ih.smul c
  | @add f g hf hg ih₁ ih₂ =>
    have e : (fun w => f w + g w) = f + g := rfl
    rw [e, fourier_add' hf.integrable hg.integrable]
    exact (ih₁.add ih₂).congr rfl

private theorem tateZeta_add {f g : ℝ → ℂ} (a : ZMod 2) (s : ℂ)
    (hf : Integrable (fun w : ℝ => f w * sgnPow a w * ((|w| : ℝ) : ℂ) ^ (s - 1)))
    (hg : Integrable (fun w : ℝ => g w * sgnPow a w * ((|w| : ℝ) : ℂ) ^ (s - 1))) :
    tateZeta (fun w => f w + g w) a s = tateZeta f a s + tateZeta g a s := by
  unfold tateZeta
  rw [show (fun w : ℝ => (f w + g w) * sgnPow a w * ((|w| : ℝ) : ℂ) ^ (s - 1))
      = (fun w : ℝ => f w * sgnPow a w * ((|w| : ℝ) : ℂ) ^ (s - 1))
        + (fun w : ℝ => g w * sgnPow a w * ((|w| : ℝ) : ℂ) ^ (s - 1)) from by
        funext w; simp only [Pi.add_apply]; ring]
  exact integral_add hf hg

private theorem InSpan.fe {f : ℝ → ℂ} (h : InSpan f) (a : ZMod 2) {s : ℂ} (hs₀ : 0 < s.re) (hs₁ : s.re < 1) :
    tateZeta (𝓕 f) a (1 - s) * Gammaℝ (s + sh a) = epsW a * Gammaℝ (1 - s + sh a) * tateZeta f a s := by
  have h1s : 0 < (1 - s).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
  induction h with
  | mem hf => exact strip_functional_equation hf a hs₀ hs₁
  | smul c _ ih =>
    rw [fourier_const_mul, tateZeta_const_mul, tateZeta_const_mul]
    linear_combination c * ih
  | @add f g hf hg ih₁ ih₂ =>
    have e : (fun w => f w + g w) = f + g := rfl
    rw [e, fourier_add' hf.integrable hg.integrable, ← e]
    have e' : (𝓕 f + 𝓕 g) = fun w => 𝓕 f w + 𝓕 g w := rfl
    rw [e', tateZeta_add a (1 - s) (hf.fourier.integrable_tate a h1s) (hg.fourier.integrable_tate a h1s),
      tateZeta_add a s (hf.integrable_tate a hs₀) (hg.integrable_tate a hs₀)]
    linear_combination ih₁ + ih₂

private theorem Cls.Z_F₁ {Ψ : ℝ → ℝ → ℂ} (h : Cls Ψ) (a₁ a₂ : ZMod 2) {w₁ w₂ : ℂ} (h0 : 0 < w₁.re) (h1 : w₁.re < 1)
    (h2 : 0 < w₂.re) :
    Z (W3.F₁ Ψ) a₁ a₂ (1 - w₁) w₂ * Gammaℝ (w₁ + sh a₁) = epsW a₁ * Gammaℝ (1 - w₁ + sh a₁) * Z Ψ a₁ a₂ w₁ w₂ := by
  have h1' : 0 < (1 - w₁).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
  rw [h.F₁.Z_eq_iterated a₁ a₂ h1' h2, h.Z_eq_iterated a₁ a₂ h0 h2, ← cint_mul_const, ← cint_const_mul]
  congr 1
  funext t
  have hfe := (h.sliceX t).fe a₁ h0 h1
  have e : (fun ξ => W3.F₁ Ψ ξ t) = 𝓕 (fun x => Ψ x t) := rfl
  rw [e]
  linear_combination (ker a₂ w₂ t) * hfe

private theorem Cls.Z_F₂ {Ψ : ℝ → ℝ → ℂ} (h : Cls Ψ) (a₁ a₂ : ZMod 2) {w₁ w₂ : ℂ} (h1 : 0 < w₁.re) (h0 : 0 < w₂.re)
    (h2 : w₂.re < 1) :
    Z (W3.F₂ Ψ) a₁ a₂ w₁ (1 - w₂) * Gammaℝ (w₂ + sh a₂) = epsW a₂ * Gammaℝ (1 - w₂ + sh a₂) * Z Ψ a₁ a₂ w₁ w₂ := by
  rw [← Z_swap Ψ, F₂_eq_swap_F₁_swap, ← Z_swap]
  exact h.swap.Z_F₁ a₂ a₁ h0 h2 h1

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

private def logprof (σlo σhi : ℝ) (x : ℝ) : ℝ :=
  (|x| ^ (σlo - 1 + σlo / 2) + |x| ^ (σhi - 1 + σlo / 2) + (|x| ^ (σlo - 1 - σlo / 2) + |x| ^ (σhi - 1 - σlo / 2)))
    / (σlo / 2)

private theorem logprof_nonneg {σlo : ℝ} (hlo : 0 < σlo) (σhi x : ℝ) : 0 ≤ logprof σlo σhi x := by
  unfold logprof; positivity

private theorem norm_ker_mul_abs_log_le (a : ZMod 2) {w : ℂ} {σlo σhi : ℝ} (h0 : 0 < σlo) (hlo : σlo ≤ w.re)
    (hhi : w.re ≤ σhi) {x : ℝ} (hx : x ≠ 0) :
    ‖ker a w x‖ * |Real.log (|x|)| ≤ logprof σlo σhi x := by
  have hr : 0 < |x| := abs_pos.mpr hx
  have hη : 0 < σlo / 2 := by positivity
  unfold ker logprof
  rw [norm_mul, norm_sgnPow a hx, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos hr, Complex.sub_re, Complex.one_re]
  calc |x| ^ (w.re - 1) * |Real.log (|x|)|
      ≤ |x| ^ (w.re - 1) * ((|x| ^ (σlo / 2) + |x| ^ (-(σlo / 2))) / (σlo / 2)) :=
        mul_le_mul_of_nonneg_left (abs_log_le_rpow_add_rpow_div hr hη) (by positivity)
    _ = (|x| ^ (w.re - 1 + σlo / 2) + |x| ^ (w.re - 1 - σlo / 2)) / (σlo / 2) := by
        rw [Real.rpow_add hr, show w.re - 1 - σlo / 2 = (w.re - 1) + (-(σlo / 2)) by ring, Real.rpow_add hr]
        ring
    _ ≤ ((|x| ^ (σlo - 1 + σlo / 2) + |x| ^ (σhi - 1 + σlo / 2))
          + (|x| ^ (σlo - 1 - σlo / 2) + |x| ^ (σhi - 1 - σlo / 2))) / (σlo / 2) := by
        gcongr
        · exact rpow_le_rpow_add_rpow hr (by linarith) (by linarith)
        · exact rpow_le_rpow_add_rpow hr (by linarith) (by linarith)

private def bigprof (σlo σhi : ℝ) (x : ℝ) : ℝ := prof σlo σhi x + logprof σlo σhi x

private theorem bigprof_nonneg {σlo : ℝ} (hlo : 0 < σlo) (σhi x : ℝ) : 0 ≤ bigprof σlo σhi x :=
  add_nonneg (prof_nonneg _ _ _) (logprof_nonneg hlo _ _)

private theorem integrable_bigprof_mul_exp {σlo σhi δ : ℝ} (hlo : 0 < σlo) (hhi : σlo ≤ σhi) (hδ : 0 < δ) :
    Integrable (fun x : ℝ => bigprof σlo σhi x * Real.exp (-δ * x ^ 2)) := by
  have hP := integrable_prof_mul_exp hlo (hlo.trans_le hhi) hδ
  have h1 := integrable_abs_rpow_mul_exp hδ (t := σlo - 1 + σlo / 2) (by linarith)
  have h2 := integrable_abs_rpow_mul_exp hδ (t := σhi - 1 + σlo / 2) (by linarith)
  have h3 := integrable_abs_rpow_mul_exp hδ (t := σlo - 1 - σlo / 2) (by linarith)
  have h4 := integrable_abs_rpow_mul_exp hδ (t := σhi - 1 - σlo / 2) (by linarith)
  have hL := (((h1.add h2).add (h3.add h4)).const_mul (σlo / 2)⁻¹)
  refine (hP.add hL).congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [bigprof, logprof, Pi.add_apply]
  field_simp

private def zintD (Ψ : ℝ → ℝ → ℂ) (a₁ a₂ : ZMod 2) (l₁ c₁ l₂ c₂ : ℂ) (w : ℂ) (p : ℝ × ℝ) : ℂ :=
  zint Ψ a₁ a₂ (l₁ * w + c₁) (l₂ * w + c₂) p
    * (l₁ * Complex.log ((|p.1| : ℝ) : ℂ) + l₂ * Complex.log ((|p.2| : ℝ) : ℂ))

private theorem hasDerivAt_ker_line (a : ZMod 2) (l c : ℂ) (w : ℂ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun w : ℂ => ker a (l * w + c) x) (ker a (l * w + c) x * Complex.log ((|x| : ℝ) : ℂ) * l) w := by
  have hf : HasDerivAt (fun w : ℂ => l * w + c - 1) l w := by
    simpa using (((hasDerivAt_id w).const_mul l).add_const c).sub_const 1
  have h0 : ((|x| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (abs_pos.mpr hx).ne'
  have h := (hf.const_cpow (Or.inl h0)).const_mul (sgnPow a x)
  unfold ker
  exact h.congr_deriv (by ring)

private theorem hasDerivAt_zint_line (Ψ : ℝ → ℝ → ℂ) (a₁ a₂ : ZMod 2) (l₁ c₁ l₂ c₂ : ℂ) {p : ℝ × ℝ} (h1 : p.1 ≠ 0)
    (h2 : p.2 ≠ 0) (w : ℂ) :
    HasDerivAt (fun w : ℂ => zint Ψ a₁ a₂ (l₁ * w + c₁) (l₂ * w + c₂) p) (zintD Ψ a₁ a₂ l₁ c₁ l₂ c₂ w p) w := by
  have hk₁ := (hasDerivAt_ker_line a₁ l₁ c₁ w h1).const_mul (Ψ p.1 p.2)
  have h : HasDerivAt (fun w : ℂ => Ψ p.1 p.2 * ker a₁ (l₁ * w + c₁) p.1 * ker a₂ (l₂ * w + c₂) p.2)
      (Ψ p.1 p.2 * (ker a₁ (l₁ * w + c₁) p.1 * Complex.log ((|p.1| : ℝ) : ℂ) * l₁) * ker a₂ (l₂ * w + c₂) p.2
        + Ψ p.1 p.2 * ker a₁ (l₁ * w + c₁) p.1
          * (ker a₂ (l₂ * w + c₂) p.2 * Complex.log ((|p.2| : ℝ) : ℂ) * l₂)) w :=
    hk₁.mul (hasDerivAt_ker_line a₂ l₂ c₂ w h2)
  unfold zintD zint
  exact h.congr_deriv (by ring)

private theorem norm_log_ofReal_abs {x : ℝ} : ‖Complex.log ((|x| : ℝ) : ℂ)‖ = |Real.log (|x|)| := by
  rw [← Complex.ofReal_log (abs_nonneg x), Complex.norm_real, Real.norm_eq_abs]

private theorem Cls.exists_dominatorD {Ψ : ℝ → ℝ → ℂ} (h : Cls Ψ) {σlo σhi : ℝ} (hlo : 0 < σlo) (hhi : σlo ≤ σhi)
    (a₁ a₂ : ZMod 2) (l₁ c₁ l₂ c₂ : ℂ) :
    ∃ D : ℝ → ℝ, Integrable D ∧
      ∀ w : ℂ, σlo ≤ (l₁ * w + c₁).re → (l₁ * w + c₁).re ≤ σhi → σlo ≤ (l₂ * w + c₂).re → (l₂ * w + c₂).re ≤ σhi →
        ∀ p : ℝ × ℝ, p.1 ≠ 0 → p.2 ≠ 0 → ‖zintD Ψ a₁ a₂ l₁ c₁ l₂ c₂ w p‖ ≤ D p.1 * D p.2 := by
  obtain ⟨C, δ, hC, hδ, hb⟩ := h.bound'
  set L : ℝ := ‖l₁‖ + ‖l₂‖ with hL
  have hL0 : 0 ≤ L := by positivity
  set K : ℝ := C * L with hK
  have hK0 : 0 ≤ K := mul_nonneg hC hL0
  refine ⟨fun x => Real.sqrt K * (bigprof σlo σhi x * Real.exp (-δ * x ^ 2)),
    (integrable_bigprof_mul_exp hlo hhi hδ).const_mul _, fun w h1 h2 h3 h4 p hp1 hp2 => ?_⟩

  set x := p.1
  set t := p.2
  have hk₁ := norm_ker_le a₁ h1 h2 x
  have hk₂ := norm_ker_le a₂ h3 h4 t
  have hkl₁ := norm_ker_mul_abs_log_le a₁ hlo h1 h2 hp1
  have hkl₂ := norm_ker_mul_abs_log_le a₂ hlo h3 h4 hp2
  have hΨ := hb x t
  have hp₁ := prof_nonneg σlo σhi x
  have hp₂ := prof_nonneg σlo σhi t
  have hl₁ := logprof_nonneg hlo σhi x
  have hl₂ := logprof_nonneg hlo σhi t
  have hn₁ := norm_nonneg (ker a₁ (l₁ * w + c₁) x)
  have hn₂ := norm_nonneg (ker a₂ (l₂ * w + c₂) t)
  have hlog₁ := abs_nonneg (Real.log |x|)
  have hlog₂ := abs_nonneg (Real.log |t|)
  have hE₁ := (Real.exp_pos (-δ * x ^ 2)).le
  have hE₂ := (Real.exp_pos (-δ * t ^ 2)).le

  have hlogfac : ‖l₁ * Complex.log ((|x| : ℝ) : ℂ) + l₂ * Complex.log ((|t| : ℝ) : ℂ)‖
      ≤ ‖l₁‖ * |Real.log (|x|)| + ‖l₂‖ * |Real.log (|t|)| := by
    calc _ ≤ ‖l₁ * Complex.log ((|x| : ℝ) : ℂ)‖ + ‖l₂ * Complex.log ((|t| : ℝ) : ℂ)‖ := norm_add_le _ _
      _ = _ := by rw [norm_mul, norm_mul, norm_log_ofReal_abs, norm_log_ofReal_abs]

  have hz : ‖zint Ψ a₁ a₂ (l₁ * w + c₁) (l₂ * w + c₂) p‖
      = ‖Ψ x t‖ * ‖ker a₁ (l₁ * w + c₁) x‖ * ‖ker a₂ (l₂ * w + c₂) t‖ := by
    simp only [zint, norm_mul]
    rfl

  have step1 : ‖zintD Ψ a₁ a₂ l₁ c₁ l₂ c₂ w p‖
      ≤ ‖Ψ x t‖ * (‖l₁‖ * ((‖ker a₁ (l₁ * w + c₁) x‖ * |Real.log (|x|)|) * ‖ker a₂ (l₂ * w + c₂) t‖)
          + ‖l₂‖ * (‖ker a₁ (l₁ * w + c₁) x‖ * (‖ker a₂ (l₂ * w + c₂) t‖ * |Real.log (|t|)|))) := by
    unfold zintD
    rw [norm_mul, hz]
    calc ‖Ψ x t‖ * ‖ker a₁ (l₁ * w + c₁) x‖ * ‖ker a₂ (l₂ * w + c₂) t‖
          * ‖l₁ * Complex.log ((|x| : ℝ) : ℂ) + l₂ * Complex.log ((|t| : ℝ) : ℂ)‖
        ≤ ‖Ψ x t‖ * ‖ker a₁ (l₁ * w + c₁) x‖ * ‖ker a₂ (l₂ * w + c₂) t‖
            * (‖l₁‖ * |Real.log (|x|)| + ‖l₂‖ * |Real.log (|t|)|) :=
          mul_le_mul_of_nonneg_left hlogfac (by positivity)
      _ = _ := by ring
  have step2 : ‖l₁‖ * ((‖ker a₁ (l₁ * w + c₁) x‖ * |Real.log (|x|)|) * ‖ker a₂ (l₂ * w + c₂) t‖)
        + ‖l₂‖ * (‖ker a₁ (l₁ * w + c₁) x‖ * (‖ker a₂ (l₂ * w + c₂) t‖ * |Real.log (|t|)|))
      ≤ L * (bigprof σlo σhi x * bigprof σlo σhi t) := by
    have e1 : (‖ker a₁ (l₁ * w + c₁) x‖ * |Real.log (|x|)|) * ‖ker a₂ (l₂ * w + c₂) t‖
        ≤ logprof σlo σhi x * prof σlo σhi t := mul_le_mul hkl₁ hk₂ hn₂ hl₁
    have e2 : ‖ker a₁ (l₁ * w + c₁) x‖ * (‖ker a₂ (l₂ * w + c₂) t‖ * |Real.log (|t|)|)
        ≤ prof σlo σhi x * logprof σlo σhi t := mul_le_mul hk₁ hkl₂ (by positivity) hp₁
    have e3 : logprof σlo σhi x * prof σlo σhi t ≤ bigprof σlo σhi x * bigprof σlo σhi t := by
      unfold bigprof; nlinarith [mul_nonneg hp₁ hp₂, mul_nonneg hl₁ hl₂, mul_nonneg hp₁ hl₂, mul_nonneg hl₁ hp₂]
    have e4 : prof σlo σhi x * logprof σlo σhi t ≤ bigprof σlo σhi x * bigprof σlo σhi t := by
      unfold bigprof; nlinarith [mul_nonneg hp₁ hp₂, mul_nonneg hl₁ hl₂, mul_nonneg hp₁ hl₂, mul_nonneg hl₁ hp₂]
    have f1 := mul_le_mul_of_nonneg_left (e1.trans e3) (norm_nonneg l₁)
    have f2 := mul_le_mul_of_nonneg_left (e2.trans e4) (norm_nonneg l₂)
    rw [hL]
    nlinarith [f1, f2]
  have hB₁ := bigprof_nonneg hlo σhi x
  have hB₂ := bigprof_nonneg hlo σhi t
  have hsq : Real.sqrt K * Real.sqrt K = K := Real.mul_self_sqrt hK0
  calc ‖zintD Ψ a₁ a₂ l₁ c₁ l₂ c₂ w p‖
      ≤ ‖Ψ x t‖ * (L * (bigprof σlo σhi x * bigprof σlo σhi t)) :=
        step1.trans (mul_le_mul_of_nonneg_left step2 (norm_nonneg _))
    _ ≤ (C * (Real.exp (-δ * x ^ 2) * Real.exp (-δ * t ^ 2))) * (L * (bigprof σlo σhi x * bigprof σlo σhi t)) :=
        mul_le_mul_of_nonneg_right hΨ (by positivity)
    _ = Real.sqrt K * (bigprof σlo σhi x * Real.exp (-δ * x ^ 2))
          * (Real.sqrt K * (bigprof σlo σhi t * Real.exp (-δ * t ^ 2))) := by
        rw [hK] at hsq
        linear_combination (-(Real.exp (-δ * x ^ 2) * Real.exp (-δ * t ^ 2) * bigprof σlo σhi x
          * bigprof σlo σhi t)) * hsq

private theorem ae_off_axes : ∀ᵐ p : ℝ × ℝ ∂((volume : Measure ℝ).prod volume), p.1 ≠ 0 ∧ p.2 ≠ 0 := by
  have hx : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by
    rw [ae_iff]
    simp
  have hm : MeasurableSet {p : ℝ × ℝ | p.1 ≠ 0 ∧ p.2 ≠ 0} :=
    ((measurableSet_eq_fun measurable_fst measurable_const).compl).inter
      ((measurableSet_eq_fun measurable_snd measurable_const).compl)
  rw [Measure.ae_prod_iff_ae_ae hm]
  exact hx.mono fun x hx' => hx.mono fun y hy => ⟨hx', hy⟩

private theorem Cls.aestronglyMeasurable_zintD {Ψ : ℝ → ℝ → ℂ} (h : Cls Ψ) (a₁ a₂ : ZMod 2) (l₁ c₁ l₂ c₂ w : ℂ) :
    AEStronglyMeasurable (zintD Ψ a₁ a₂ l₁ c₁ l₂ c₂ w) ((volume : Measure ℝ).prod volume) := by
  have hlog : Measurable fun p : ℝ × ℝ =>
      l₁ * Complex.log ((|p.1| : ℝ) : ℂ) + l₂ * Complex.log ((|p.2| : ℝ) : ℂ) :=
    ((Complex.measurable_log.comp (Complex.measurable_ofReal.comp (measurable_abs.comp measurable_fst))).const_mul
      l₁).add
      ((Complex.measurable_log.comp (Complex.measurable_ofReal.comp (measurable_abs.comp measurable_snd))).const_mul
        l₂)
  exact (h.aestronglyMeasurable_zint a₁ a₂ _ _).mul hlog.aestronglyMeasurable

private theorem Cls.differentiableAt_Z_line {Ψ : ℝ → ℝ → ℂ} (h : Cls Ψ) (a₁ a₂ : ZMod 2) (l₁ c₁ l₂ c₂ : ℂ) {w₀ : ℂ}
    (h₁ : 0 < (l₁ * w₀ + c₁).re) (h₂ : 0 < (l₂ * w₀ + c₂).re) :
    DifferentiableAt ℂ (fun w => Z Ψ a₁ a₂ (l₁ * w + c₁) (l₂ * w + c₂)) w₀ := by

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
  obtain ⟨D, hD, hDb⟩ := h.exists_dominatorD hρ0 hρσ a₁ a₂ l₁ c₁ l₂ c₂
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (volume : Measure ℝ).prod volume)
    (F := fun w p => zint Ψ a₁ a₂ (l₁ * w + c₁) (l₂ * w + c₂) p) (F' := zintD Ψ a₁ a₂ l₁ c₁ l₂ c₂) (x₀ := w₀)
    (bound := fun p : ℝ × ℝ => D p.1 * D p.2) (Metric.ball_mem_nhds w₀ hr0)
    (Filter.Eventually.of_forall fun w => h.aestronglyMeasurable_zint a₁ a₂ _ _) (h.integrable_zint a₁ a₂ h₁ h₂)
    (h.aestronglyMeasurable_zintD a₁ a₂ l₁ c₁ l₂ c₂ w₀)
    (ae_off_axes.mono fun p hp w hw => by
      obtain ⟨r₁, r₂, r₃, r₄⟩ := hrange w hw
      exact hDb w r₁ r₂ r₃ r₄ p hp.1 hp.2)
    (hD.mul_prod hD)
    (ae_off_axes.mono fun p hp w _ => hasDerivAt_zint_line Ψ a₁ a₂ l₁ c₁ l₂ c₂ hp.1 hp.2 w)
  exact key.2.differentiableAt

private theorem Cls.differentiableOn_Z_line {Ψ : ℝ → ℝ → ℂ} (h : Cls Ψ) (a₁ a₂ : ZMod 2) (l₁ c₁ l₂ c₂ : ℂ) :
    DifferentiableOn ℂ (fun w => Z Ψ a₁ a₂ (l₁ * w + c₁) (l₂ * w + c₂))
      {w : ℂ | 0 < (l₁ * w + c₁).re ∧ 0 < (l₂ * w + c₂).re} :=
  fun _ hw => (h.differentiableAt_Z_line a₁ a₂ l₁ c₁ l₂ c₂ hw.1 hw.2).differentiableWithinAt

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

private def Echart (Ψ : ℝ → ℝ → ℂ) (a₁ a₂ : ZMod 2) (w₁ w₂ : ℂ) : ℂ :=
  Z Ψ a₁ a₂ w₁ w₂ * (Gammaℝ (w₁ + sh a₁))⁻¹ * (Gammaℝ (w₂ + sh a₂))⁻¹

private theorem sh_re (a : ZMod 2) : (sh a).re = if a = 0 then 0 else 1 := by
  unfold sh; split_ifs <;> simp

private theorem sh_re_nonneg (a : ZMod 2) : 0 ≤ (sh a).re := by
  rw [sh_re]; split_ifs <;> norm_num

private theorem sh_im (a : ZMod 2) : (sh a).im = 0 := by
  unfold sh; split_ifs <;> simp

private theorem Gammaℝ_add_sh_ne_zero {w : ℂ} (hw : 0 < w.re) (a : ZMod 2) : Gammaℝ (w + sh a) ≠ 0 :=
  Gammaℝ_ne_zero_of_re_pos (by rw [Complex.add_re]; linarith [sh_re_nonneg a])

private theorem Cls.differentiableAt_Echart_line {Ψ : ℝ → ℝ → ℂ} (h : Cls Ψ) (a₁ a₂ : ZMod 2) (l₁ c₁ l₂ c₂ : ℂ)
    {w₀ : ℂ} (h₁ : 0 < (l₁ * w₀ + c₁).re) (h₂ : 0 < (l₂ * w₀ + c₂).re) :
    DifferentiableAt ℂ (fun w => Echart Ψ a₁ a₂ (l₁ * w + c₁) (l₂ * w + c₂)) w₀ := by
  unfold Echart
  have g₁ : DifferentiableAt ℂ (fun w => (Gammaℝ (l₁ * w + c₁ + sh a₁))⁻¹) w₀ :=
    (differentiable_Gammaℝ_inv _).comp w₀ (by fun_prop)
  have g₂ : DifferentiableAt ℂ (fun w => (Gammaℝ (l₂ * w + c₂ + sh a₂))⁻¹) w₀ :=
    (differentiable_Gammaℝ_inv _).comp w₀ (by fun_prop)
  exact ((h.differentiableAt_Z_line a₁ a₂ l₁ c₁ l₂ c₂ h₁ h₂).mul g₁).mul g₂

private theorem Cls.Echart_F₁ {Ψ : ℝ → ℝ → ℂ} (h : Cls Ψ) (a₁ a₂ : ZMod 2) {w₁ w₂ : ℂ} (h0 : 0 < w₁.re)
    (h1 : w₁.re < 1)
    (h2 : 0 < w₂.re) : Echart (W3.F₁ Ψ) a₁ a₂ (1 - w₁) w₂ = epsW a₁ * Echart Ψ a₁ a₂ w₁ w₂ := by
  have hZ := h.Z_F₁ a₁ a₂ h0 h1 h2
  have hg₁ := Gammaℝ_add_sh_ne_zero h0 a₁
  have hg₁' : Gammaℝ (1 - w₁ + sh a₁) ≠ 0 :=
    Gammaℝ_add_sh_ne_zero (by simp only [Complex.sub_re, Complex.one_re]; linarith) a₁
  have hg₂ := Gammaℝ_add_sh_ne_zero h2 a₂
  unfold Echart
  rw [(eq_mul_inv_iff_mul_eq₀ hg₁).mpr hZ]
  field_simp

private theorem Cls.Echart_F₂ {Ψ : ℝ → ℝ → ℂ} (h : Cls Ψ) (a₁ a₂ : ZMod 2) {w₁ w₂ : ℂ} (h1 : 0 < w₁.re)
    (h0 : 0 < w₂.re)
    (h2 : w₂.re < 1) : Echart (W3.F₂ Ψ) a₁ a₂ w₁ (1 - w₂) = epsW a₂ * Echart Ψ a₁ a₂ w₁ w₂ := by
  have hZ := h.Z_F₂ a₁ a₂ h1 h0 h2
  have hg₁ := Gammaℝ_add_sh_ne_zero h1 a₁
  have hg₂ := Gammaℝ_add_sh_ne_zero h0 a₂
  have hg₂' : Gammaℝ (1 - w₂ + sh a₂) ≠ 0 :=
    Gammaℝ_add_sh_ne_zero (by simp only [Complex.sub_re, Complex.one_re]; linarith) a₂
  unfold Echart
  rw [(eq_mul_inv_iff_mul_eq₀ hg₂).mpr hZ]
  field_simp

private noncomputable def E₁ (Ψ : ℝ → ℝ → ℂ) (a₁ a₂ : ZMod 2) (w₁ w₂ : ℂ) : ℂ :=
  if 0 < w₁.re then Echart Ψ a₁ a₂ w₁ w₂ else (epsW a₁)⁻¹ * Echart (W3.F₁ Ψ) a₁ a₂ (1 - w₁) w₂

private theorem E₁_of_re_pos (Ψ : ℝ → ℝ → ℂ) (a₁ a₂ : ZMod 2) {w₁ : ℂ} (h1 : 0 < w₁.re) (w₂ : ℂ) :
    E₁ Ψ a₁ a₂ w₁ w₂ = Echart Ψ a₁ a₂ w₁ w₂ := if_pos h1

private theorem Cls.E₁_of_re_lt_one {Ψ : ℝ → ℝ → ℂ} (h : Cls Ψ) (a₁ a₂ : ZMod 2) {w₁ w₂ : ℂ} (h1 : w₁.re < 1)
    (h2 : 0 < w₂.re) : E₁ Ψ a₁ a₂ w₁ w₂ = (epsW a₁)⁻¹ * Echart (W3.F₁ Ψ) a₁ a₂ (1 - w₁) w₂ := by
  unfold E₁
  split_ifs with h0
  · rw [h.Echart_F₁ a₁ a₂ h0 h1 h2, ← mul_assoc, inv_mul_cancel₀ (epsW_ne_zero a₁), one_mul]
  · rfl

private theorem Cls.differentiableAt_E₁_line {Ψ : ℝ → ℝ → ℂ} (h : Cls Ψ) (a₁ a₂ : ZMod 2) (l₁ c₁ l₂ c₂ : ℂ) {w₀ : ℂ}
    (h₂ : 0 < (l₂ * w₀ + c₂).re) :
    DifferentiableAt ℂ (fun w => E₁ Ψ a₁ a₂ (l₁ * w + c₁) (l₂ * w + c₂)) w₀ := by
  have cont₁ : Continuous fun w : ℂ => (l₁ * w + c₁).re := by fun_prop
  have cont₂ : Continuous fun w : ℂ => (l₂ * w + c₂).re := by fun_prop
  have ev₂ : ∀ᶠ w in 𝓝 w₀, 0 < (l₂ * w + c₂).re :=
    (continuousAt_const).eventually_lt cont₂.continuousAt h₂
  by_cases h₁ : 0 < (l₁ * w₀ + c₁).re
  · have ev₁ : ∀ᶠ w in 𝓝 w₀, 0 < (l₁ * w + c₁).re := (continuousAt_const).eventually_lt cont₁.continuousAt h₁
    refine (h.differentiableAt_Echart_line a₁ a₂ l₁ c₁ l₂ c₂ h₁ h₂).congr_of_eventuallyEq ?_
    exact ev₁.mono fun w hw => E₁_of_re_pos Ψ a₁ a₂ hw _
  · have h₁' : (l₁ * w₀ + c₁).re < 1 := by have := not_lt.mp h₁; linarith
    have ev₁ : ∀ᶠ w in 𝓝 w₀, (l₁ * w + c₁).re < 1 := cont₁.continuousAt.eventually_lt continuousAt_const h₁'

    have hd : DifferentiableAt ℂ (fun w => (epsW a₁)⁻¹ * Echart (W3.F₁ Ψ) a₁ a₂ (-l₁ * w + (1 - c₁)) (l₂ * w + c₂))
        w₀ := by
      refine (h.F₁.differentiableAt_Echart_line a₁ a₂ (-l₁) (1 - c₁) l₂ c₂ ?_ h₂).const_mul _
      have e : -l₁ * w₀ + (1 - c₁) = 1 - (l₁ * w₀ + c₁) := by ring
      rw [e, Complex.sub_re, Complex.one_re]; linarith
    refine hd.congr_of_eventuallyEq ?_
    refine (ev₁.and ev₂).mono fun w ⟨hw₁, hw₂⟩ => ?_
    beta_reduce
    rw [h.E₁_of_re_lt_one a₁ a₂ hw₁ hw₂]
    congr 2
    ring

private theorem Cls.E₁_F₂ {Ψ : ℝ → ℝ → ℂ} (h : Cls Ψ) (a₁ a₂ : ZMod 2) {w₂ : ℂ} (h0 : 0 < w₂.re) (h2 : w₂.re < 1)
    (w₁ : ℂ) : E₁ (W3.F₂ Ψ) a₁ a₂ w₁ (1 - w₂) = epsW a₂ * E₁ Ψ a₁ a₂ w₁ w₂ := by
  have h1w : 0 < (1 - w₂).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
  have df : Differentiable ℂ fun w₁ => E₁ (W3.F₂ Ψ) a₁ a₂ w₁ (1 - w₂) := fun w => by
    have := h.F₂.differentiableAt_E₁_line a₁ a₂ 1 0 0 (1 - w₂) (w₀ := w) (by simpa using h1w)
    simpa using this
  have dg : Differentiable ℂ fun w₁ => epsW a₂ * E₁ Ψ a₁ a₂ w₁ w₂ := fun w => by
    have := h.differentiableAt_E₁_line a₁ a₂ 1 0 0 w₂ (w₀ := w) (by simpa using h0)
    simpa using this.const_mul (epsW a₂)
  have e := entire_eq_of_eqOn_open df dg isOpen_re_pos (z₀ := 1) (by simp) fun z hz => by
    simp only [Set.mem_setOf_eq] at hz
    rw [E₁_of_re_pos _ a₁ a₂ hz, E₁_of_re_pos _ a₁ a₂ hz, h.Echart_F₂ a₁ a₂ hz h0 h2]
  exact congrFun e w₁

private noncomputable def E (Ψ : ℝ → ℝ → ℂ) (a₁ a₂ : ZMod 2) (w₁ w₂ : ℂ) : ℂ :=
  if 0 < w₂.re then E₁ Ψ a₁ a₂ w₁ w₂ else (epsW a₂)⁻¹ * E₁ (W3.F₂ Ψ) a₁ a₂ w₁ (1 - w₂)

private theorem E_of_re_pos (Ψ : ℝ → ℝ → ℂ) (a₁ a₂ : ZMod 2) (w₁ : ℂ) {w₂ : ℂ} (h2 : 0 < w₂.re) :
    E Ψ a₁ a₂ w₁ w₂ = E₁ Ψ a₁ a₂ w₁ w₂ := if_pos h2

private theorem Cls.E_of_re_lt_one {Ψ : ℝ → ℝ → ℂ} (h : Cls Ψ) (a₁ a₂ : ZMod 2) (w₁ : ℂ) {w₂ : ℂ} (h2 : w₂.re < 1) :
    E Ψ a₁ a₂ w₁ w₂ = (epsW a₂)⁻¹ * E₁ (W3.F₂ Ψ) a₁ a₂ w₁ (1 - w₂) := by
  unfold E
  split_ifs with h0
  · rw [h.E₁_F₂ a₁ a₂ h0 h2 w₁, ← mul_assoc, inv_mul_cancel₀ (epsW_ne_zero a₂), one_mul]
  · rfl

private theorem Z_eq_E (Ψ : ℝ → ℝ → ℂ) (a₁ a₂ : ZMod 2) {w₁ w₂ : ℂ} (h₁ : 0 < w₁.re) (h₂ : 0 < w₂.re) :
    Z Ψ a₁ a₂ w₁ w₂ = Gammaℝ (w₁ + sh a₁) * Gammaℝ (w₂ + sh a₂) * E Ψ a₁ a₂ w₁ w₂ := by
  rw [E_of_re_pos _ _ _ _ h₂, E₁_of_re_pos _ _ _ h₁]
  unfold Echart
  have hg₁ := Gammaℝ_add_sh_ne_zero h₁ a₁
  have hg₂ := Gammaℝ_add_sh_ne_zero h₂ a₂
  field_simp

private theorem Cls.differentiable_E_line {Ψ : ℝ → ℝ → ℂ} (h : Cls Ψ) (a₁ a₂ : ZMod 2) (l₁ c₁ l₂ c₂ : ℂ) :
    Differentiable ℂ fun w => E Ψ a₁ a₂ (l₁ * w + c₁) (l₂ * w + c₂) := by
  intro w₀
  have cont₂ : Continuous fun w : ℂ => (l₂ * w + c₂).re := by fun_prop
  by_cases h₂ : 0 < (l₂ * w₀ + c₂).re
  · have ev₂ : ∀ᶠ w in 𝓝 w₀, 0 < (l₂ * w + c₂).re := (continuousAt_const).eventually_lt cont₂.continuousAt h₂
    refine (h.differentiableAt_E₁_line a₁ a₂ l₁ c₁ l₂ c₂ h₂).congr_of_eventuallyEq ?_
    exact ev₂.mono fun w hw => E_of_re_pos Ψ a₁ a₂ _ hw
  · have h₂' : (l₂ * w₀ + c₂).re < 1 := by have := not_lt.mp h₂; linarith
    have ev₂ : ∀ᶠ w in 𝓝 w₀, (l₂ * w + c₂).re < 1 := cont₂.continuousAt.eventually_lt continuousAt_const h₂'
    have hd : DifferentiableAt ℂ
        (fun w => (epsW a₂)⁻¹ * E₁ (W3.F₂ Ψ) a₁ a₂ (l₁ * w + c₁) (-l₂ * w + (1 - c₂))) w₀ := by
      refine (h.F₂.differentiableAt_E₁_line a₁ a₂ l₁ c₁ (-l₂) (1 - c₂) ?_).const_mul _
      have e : -l₂ * w₀ + (1 - c₂) = 1 - (l₂ * w₀ + c₂) := by ring
      rw [e, Complex.sub_re, Complex.one_re]; linarith
    refine hd.congr_of_eventuallyEq ?_
    refine ev₂.mono fun w hw => ?_
    beta_reduce
    rw [h.E_of_re_lt_one a₁ a₂ _ hw]
    congr 2
    ring

private theorem Cls.differentiable_E_comp {Ψ : ℝ → ℝ → ℂ} (h : Cls Ψ) (a₁ a₂ : ZMod 2) {f₁ f₂ : ℂ → ℂ}
    (l₁ c₁ l₂ c₂ : ℂ)
    (e₁ : ∀ w, f₁ w = l₁ * w + c₁) (e₂ : ∀ w, f₂ w = l₂ * w + c₂) :
    Differentiable ℂ fun w => E Ψ a₁ a₂ (f₁ w) (f₂ w) := by
  have e : (fun w => E Ψ a₁ a₂ (f₁ w) (f₂ w)) = fun w => E Ψ a₁ a₂ (l₁ * w + c₁) (l₂ * w + c₂) :=
    funext fun w => by rw [e₁, e₂]
  rw [e]
  exact h.differentiable_E_line a₁ a₂ l₁ c₁ l₂ c₂

private theorem Cls.differentiable_E_fst {Ψ : ℝ → ℝ → ℂ} (h : Cls Ψ) (a₁ a₂ : ZMod 2) (w₂ : ℂ) :
    Differentiable ℂ fun w₁ => E Ψ a₁ a₂ w₁ w₂ :=
  h.differentiable_E_comp a₁ a₂ 1 0 0 w₂ (fun w => by ring) (fun w => by ring)

private theorem Cls.differentiable_E_snd {Ψ : ℝ → ℝ → ℂ} (h : Cls Ψ) (a₁ a₂ : ZMod 2) (w₁ : ℂ) :
    Differentiable ℂ fun w₂ => E Ψ a₁ a₂ w₁ w₂ :=
  h.differentiable_E_comp a₁ a₂ 0 w₁ 1 0 (fun w => by ring) (fun w => by ring)

private theorem Cls.ext_E {f g : ℂ → ℂ → ℂ}
    (hf₁ : ∀ w₂, Differentiable ℂ fun w₁ => f w₁ w₂) (hg₁ : ∀ w₂, Differentiable ℂ fun w₁ => g w₁ w₂)
    (hf₂ : ∀ w₁, Differentiable ℂ fun w₂ => f w₁ w₂) (hg₂ : ∀ w₁, Differentiable ℂ fun w₂ => g w₁ w₂)
    (h : ∀ w₁ w₂, 0 < w₁.re → 0 < w₂.re → f w₁ w₂ = g w₁ w₂) : ∀ w₁ w₂, f w₁ w₂ = g w₁ w₂ :=
  ext_of_eqOn_rect hf₁ hg₁ hf₂ hg₂ isOpen_re_pos isOpen_re_pos (z₁ := 1) (z₂ := 1) (by simp) (by simp)
    fun w₁ h₁ w₂ h₂ => h w₁ w₂ h₁ h₂

private theorem Cls.E_F₁ {Ψ : ℝ → ℝ → ℂ} (h : Cls Ψ) (a₁ a₂ : ZMod 2) (w₁ w₂ : ℂ) :
    E (W3.F₁ Ψ) a₁ a₂ (1 - w₁) w₂ = epsW a₁ * E Ψ a₁ a₂ w₁ w₂ := by
  refine ext_of_eqOn_rect (f := fun w₁ w₂ => E (W3.F₁ Ψ) a₁ a₂ (1 - w₁) w₂)
    (g := fun w₁ w₂ => epsW a₁ * E Ψ a₁ a₂ w₁ w₂)
    (fun w₂ => h.F₁.differentiable_E_comp a₁ a₂ (-1) 1 0 w₂ (fun w => by ring) (fun w => by ring))
    (fun w₂ => (h.differentiable_E_fst a₁ a₂ w₂).const_mul _)
    (fun w₁ => h.F₁.differentiable_E_comp a₁ a₂ 0 (1 - w₁) 1 0 (fun w => by ring) (fun w => by ring))
    (fun w₁ => (h.differentiable_E_snd a₁ a₂ w₁).const_mul _)
    isOpen_re_lt_one isOpen_re_pos (z₁ := 0) (z₂ := 1) (by simp) (by simp) ?_ w₁ w₂
  intro u₁ hu₁ u₂ hu₂
  simp only [Set.mem_setOf_eq] at hu₁ hu₂
  have h1u : 0 < (1 - u₁).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
  try simp only
  rw [E_of_re_pos _ _ _ _ hu₂, E₁_of_re_pos _ _ _ h1u, E_of_re_pos _ _ _ _ hu₂, h.E₁_of_re_lt_one a₁ a₂ hu₁ hu₂,
    ← mul_assoc, mul_inv_cancel₀ (epsW_ne_zero a₁), one_mul]

private theorem Cls.E_F₂ {Ψ : ℝ → ℝ → ℂ} (h : Cls Ψ) (a₁ a₂ : ZMod 2) (w₁ w₂ : ℂ) :
    E (W3.F₂ Ψ) a₁ a₂ w₁ (1 - w₂) = epsW a₂ * E Ψ a₁ a₂ w₁ w₂ := by
  have df : Differentiable ℂ fun w₂ => E (W3.F₂ Ψ) a₁ a₂ w₁ (1 - w₂) :=
    h.F₂.differentiable_E_comp a₁ a₂ 0 w₁ (-1) 1 (fun w => by ring) (fun w => by ring)
  have dg : Differentiable ℂ fun w₂ => epsW a₂ * E Ψ a₁ a₂ w₁ w₂ := (h.differentiable_E_snd a₁ a₂ w₁).const_mul _
  have e := entire_eq_of_eqOn_open df dg isOpen_re_lt_one (z₀ := 0) (by simp) fun u hu => by
    simp only [Set.mem_setOf_eq] at hu
    have h1u : 0 < (1 - u).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
    rw [E_of_re_pos _ _ _ _ h1u, h.E_of_re_lt_one a₁ a₂ w₁ hu, ← mul_assoc, mul_inv_cancel₀ (epsW_ne_zero a₂),
      one_mul]
  exact congrFun e w₂

private theorem Cls.E_swap {Ψ : ℝ → ℝ → ℂ} (h : Cls Ψ) (a₁ a₂ : ZMod 2) (w₁ w₂ : ℂ) :
    E (fun x t => Ψ t x) a₂ a₁ w₂ w₁ = E Ψ a₁ a₂ w₁ w₂ := by
  refine Cls.ext_E (f := fun w₁ w₂ => E (fun x t => Ψ t x) a₂ a₁ w₂ w₁) (g := fun w₁ w₂ => E Ψ a₁ a₂ w₁ w₂)
    (fun w₂ => h.swap.differentiable_E_snd a₂ a₁ w₂) (fun w₂ => h.differentiable_E_fst a₁ a₂ w₂)
    (fun w₁ => h.swap.differentiable_E_fst a₂ a₁ w₁) (fun w₁ => h.differentiable_E_snd a₁ a₂ w₁) ?_ w₁ w₂
  intro u₁ u₂ h₁ h₂
  try simp only
  rw [E_of_re_pos _ _ _ _ h₁, E₁_of_re_pos _ _ _ h₂, E_of_re_pos _ _ _ _ h₂, E₁_of_re_pos _ _ _ h₁]
  unfold Echart
  rw [Z_swap]
  ring

private theorem Z_smul (c : ℂ) (Ψ : ℝ → ℝ → ℂ) (a₁ a₂ : ZMod 2) (w₁ w₂ : ℂ) :
    Z (fun x t => c * Ψ x t) a₁ a₂ w₁ w₂ = c * Z Ψ a₁ a₂ w₁ w₂ := by
  unfold Z
  have e : zint (fun x t => c * Ψ x t) a₁ a₂ w₁ w₂ = fun p => c * zint Ψ a₁ a₂ w₁ w₂ p := by
    funext p; simp only [zint]; ring
  rw [e]
  exact integral_const_mul c (zint Ψ a₁ a₂ w₁ w₂)

private theorem Cls.E_smul {Ψ : ℝ → ℝ → ℂ} (h : Cls Ψ) (c : ℂ) (a₁ a₂ : ZMod 2) (w₁ w₂ : ℂ) :
    E (fun x t => c * Ψ x t) a₁ a₂ w₁ w₂ = c * E Ψ a₁ a₂ w₁ w₂ := by
  refine Cls.ext_E (f := fun w₁ w₂ => E (fun x t => c * Ψ x t) a₁ a₂ w₁ w₂) (g := fun w₁ w₂ => c * E Ψ a₁ a₂ w₁ w₂)
    (fun w₂ => (h.smul c).differentiable_E_fst a₁ a₂ w₂) (fun w₂ => (h.differentiable_E_fst a₁ a₂ w₂).const_mul _)
    (fun w₁ => (h.smul c).differentiable_E_snd a₁ a₂ w₁) (fun w₁ => (h.differentiable_E_snd a₁ a₂ w₁).const_mul _)
    ?_ w₁ w₂
  intro u₁ u₂ h₁ h₂
  try simp only
  rw [E_of_re_pos _ _ _ _ h₂, E₁_of_re_pos _ _ _ h₁, E_of_re_pos _ _ _ _ h₂, E₁_of_re_pos _ _ _ h₁]
  unfold Echart
  rw [Z_smul]
  ring

end W3

namespace W3

private def sgnW (b : ZMod 2) : ℂ := (-1) ^ (if b = 0 then 0 else 1 : ℕ)

private theorem gen_reflX (α₁ α₂ γr γi : ℝ) (β₁ β₂ : ℂ) :
    gen α₁ α₂ (-γr) (-γi) (-β₁) β₂ = fun x t => gen α₁ α₂ γr γi β₁ β₂ (-x) t := by
  funext x t
  unfold gen gexp
  congr 1
  push_cast
  ring

private theorem Cls.reflX {Ψ : ℝ → ℝ → ℂ} (h : Cls Ψ) : Cls (fun x t => Ψ (-x) t) := by
  induction h with
  | @gen α₁ α₂ γr γi β₁ β₂ hadm =>
    refine (Cls.gen (-β₁) β₂ ⟨hadm.h₁, hadm.h₂, ?_, ?_⟩).congr (gen_reflX α₁ α₂ γr γi β₁ β₂)
    · have := hadm.hγ; linear_combination this
    · have := hadm.hpd; nlinarith [this]
  | smul c _ ih => exact ih.smul c
  | add _ _ ih₁ ih₂ => exact ih₁.add ih₂
  | mulX _ ih =>
    refine (ih.mulX.smul (-1)).congr ?_
    funext x t
    push_cast
    ring
  | mulT _ ih => exact ih.mulT

private theorem sgnPow_neg (a : ZMod 2) (w : ℝ) : sgnPow a (-w) = sgnW a * sgnPow a w := by
  unfold sgnPow sgnW
  split_ifs with ha
  · simp
  · rw [Left.sign_neg]
    push_cast
    ring

private theorem tateZeta_reflX (f : ℝ → ℂ) (a : ZMod 2) (s : ℂ) :
    tateZeta (fun w => f (-w)) a s = sgnW a * tateZeta f a s := by
  unfold tateZeta
  have e1 : (fun w : ℝ => f (-w) * sgnPow a w * ((|w| : ℝ) : ℂ) ^ (s - 1))
      = fun w : ℝ => (fun u : ℝ => f u * sgnPow a (-u) * ((|(-u)| : ℝ) : ℂ) ^ (s - 1)) (-w) := by
    funext w; simp only [neg_neg]
  rw [e1]
  have hneg : (∫ w : ℝ, (fun u : ℝ => f u * sgnPow a (-u) * ((|(-u)| : ℝ) : ℂ) ^ (s - 1)) (-w))
      = ∫ u : ℝ, (fun u : ℝ => f u * sgnPow a (-u) * ((|(-u)| : ℝ) : ℂ) ^ (s - 1)) u :=
    integral_neg_eq_self (fun u : ℝ => f u * sgnPow a (-u) * ((|(-u)| : ℝ) : ℂ) ^ (s - 1)) volume
  rw [hneg]
  have e2 : (fun u : ℝ => f u * sgnPow a (-u) * ((|(-u)| : ℝ) : ℂ) ^ (s - 1))
      = fun u : ℝ => sgnW a * (f u * sgnPow a u * ((|u| : ℝ) : ℂ) ^ (s - 1)) := by
    funext u; rw [sgnPow_neg, abs_neg]; ring
  rw [e2]
  exact cint_const_mul _ _

private theorem Cls.Z_reflX {Ψ : ℝ → ℝ → ℂ} (h : Cls Ψ) (a₁ a₂ : ZMod 2) {w₁ w₂ : ℂ} (h₁ : 0 < w₁.re)
    (h₂ : 0 < w₂.re) :
    Z (fun x t => Ψ (-x) t) a₁ a₂ w₁ w₂ = sgnW a₁ * Z Ψ a₁ a₂ w₁ w₂ := by
  rw [h.reflX.Z_eq_iterated a₁ a₂ h₁ h₂, h.Z_eq_iterated a₁ a₂ h₁ h₂, ← cint_const_mul]
  congr 1
  funext t
  rw [tateZeta_reflX (fun x => Ψ x t)]
  ring

private theorem Cls.E_reflX {Ψ : ℝ → ℝ → ℂ} (h : Cls Ψ) (a₁ a₂ : ZMod 2) (w₁ w₂ : ℂ) :
    E (fun x t => Ψ (-x) t) a₁ a₂ w₁ w₂ = sgnW a₁ * E Ψ a₁ a₂ w₁ w₂ := by
  refine Cls.ext_E (f := fun w₁ w₂ => E (fun x t => Ψ (-x) t) a₁ a₂ w₁ w₂)
    (g := fun w₁ w₂ => sgnW a₁ * E Ψ a₁ a₂ w₁ w₂)
    (fun w₂ => h.reflX.differentiable_E_fst a₁ a₂ w₂) (fun w₂ => (h.differentiable_E_fst a₁ a₂ w₂).const_mul _)
    (fun w₁ => h.reflX.differentiable_E_snd a₁ a₂ w₁) (fun w₁ => (h.differentiable_E_snd a₁ a₂ w₁).const_mul _)
    ?_ w₁ w₂
  intro u₁ u₂ h₁ h₂
  try simp only
  rw [E_of_re_pos _ _ _ _ h₂, E₁_of_re_pos _ _ _ h₁, E_of_re_pos _ _ _ _ h₂, E₁_of_re_pos _ _ _ h₁]
  unfold Echart
  rw [h.Z_reflX a₁ a₂ h₁ h₂]
  ring

private theorem norm_epsW (a : ZMod 2) : ‖epsW a‖ = 1 := by
  unfold epsW; rw [norm_pow, norm_neg, Complex.norm_I, one_pow]

private theorem norm_epsW_inv_mul (a : ZMod 2) (z : ℂ) : ‖(epsW a)⁻¹ * z‖ = ‖z‖ := by
  rw [norm_mul, norm_inv, norm_epsW, inv_one, one_mul]

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

private theorem Cls.exists_Echart_bound {Ψ : ℝ → ℝ → ℂ} (h : Cls Ψ) {R : ℝ} (hR : 1 / 2 ≤ R) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ (a₁ a₂ : ZMod 2) (v₁ v₂ : ℂ), 1 / 2 ≤ v₁.re → v₁.re ≤ R → 1 / 2 ≤ v₂.re →
      v₂.re ≤ R → ‖Echart Ψ a₁ a₂ v₁ v₂‖ ≤ A * Real.exp (B * (|v₁.im| + |v₂.im|)) := by
  obtain ⟨M, hM⟩ := h.exists_Z_bound (σlo := 1 / 2) (σhi := R) (by norm_num) (by linarith)
  obtain ⟨C, D, hC, hD, hCD⟩ := exists_bound_invGammaℝ_strip' (1 / 2) (R + 1)
  refine ⟨|M| * C * C, D, by positivity, hD, fun a₁ a₂ v₁ v₂ h1 h2 h3 h4 => ?_⟩
  have g₁ := hCD (v₁ + sh a₁) (by rw [Complex.add_re]; linarith [sh_re_nonneg a₁])
    (by rw [Complex.add_re, sh_re]; split_ifs <;> linarith)
  have g₂ := hCD (v₂ + sh a₂) (by rw [Complex.add_re]; linarith [sh_re_nonneg a₂])
    (by rw [Complex.add_re, sh_re]; split_ifs <;> linarith)
  rw [Complex.add_im, sh_im, add_zero] at g₁ g₂
  have hZ : ‖Z Ψ a₁ a₂ v₁ v₂‖ ≤ |M| := (hM a₁ a₂ v₁ v₂ h1 h2 h3 h4).trans (le_abs_self M)
  unfold Echart
  rw [norm_mul, norm_mul]
  calc ‖Z Ψ a₁ a₂ v₁ v₂‖ * ‖(Gammaℝ (v₁ + sh a₁))⁻¹‖ * ‖(Gammaℝ (v₂ + sh a₂))⁻¹‖
      ≤ |M| * (C * Real.exp (D * |v₁.im|)) * (C * Real.exp (D * |v₂.im|)) := by
        gcongr
    _ = |M| * C * C * Real.exp (D * (|v₁.im| + |v₂.im|)) := by
        rw [mul_add, Real.exp_add]; ring

private theorem Cls.exists_E_strip_bound {Ψ : ℝ → ℝ → ℂ} (h : Cls Ψ) (a₁ a₂ : ZMod 2) (c₁ c₂ : ℂ) (σ₁ σ₂ : ℝ) :
    ∃ A B : ℝ, ∀ w : ℂ, σ₁ ≤ w.re → w.re ≤ σ₂ →
      ‖E Ψ a₁ a₂ (w + c₁) (w + c₂)‖ ≤ A * Real.exp (B * |w.im|) := by

  set R : ℝ := |σ₁| + |σ₂| + ‖c₁‖ + ‖c₂‖ + 2 with hR
  have hR' : 1 / 2 ≤ R := by have := norm_nonneg c₁; have := norm_nonneg c₂; have := abs_nonneg σ₁
                             have := abs_nonneg σ₂; rw [hR]; linarith
  obtain ⟨A₁, B₁, hA₁, hB₁, b₁⟩ := h.exists_Echart_bound hR'
  obtain ⟨A₂, B₂, hA₂, hB₂, b₂⟩ := h.F₁.exists_Echart_bound hR'
  obtain ⟨A₃, B₃, hA₃, hB₃, b₃⟩ := h.F₂.exists_Echart_bound hR'
  obtain ⟨A₄, B₄, hA₄, hB₄, b₄⟩ := h.F₂.F₁.exists_Echart_bound hR'
  set A₀ : ℝ := A₁ + A₂ + A₃ + A₄ with hA₀
  set B₀ : ℝ := B₁ + B₂ + B₃ + B₄ with hB₀
  have hB₀0 : 0 ≤ B₀ := by rw [hB₀]; linarith

  have weaken : ∀ (Aᵢ Bᵢ : ℝ), 0 ≤ Aᵢ → Aᵢ ≤ A₀ → Bᵢ ≤ B₀ → ∀ (X : ℝ) (S : ℝ), 0 ≤ S →
      X ≤ Aᵢ * Real.exp (Bᵢ * S) → X ≤ A₀ * Real.exp (B₀ * S) := by
    intro Aᵢ Bᵢ _ hA hB X S hS hX
    refine hX.trans (mul_le_mul hA (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hB hS)) (Real.exp_pos _).le
      (by rw [hA₀]; linarith))
  refine ⟨A₀ * Real.exp (B₀ * (‖c₁‖ + ‖c₂‖)), 2 * B₀, fun w hw₁ hw₂ => ?_⟩

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

  have tail : A₀ * Real.exp (B₀ * (|u₁.im| + |u₂.im|))
      ≤ A₀ * Real.exp (B₀ * (‖c₁‖ + ‖c₂‖)) * Real.exp (2 * B₀ * |w.im|) := by
    rw [mul_assoc, ← Real.exp_add]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by rw [hA₀]; positivity)
    nlinarith [mul_le_mul_of_nonneg_left (add_le_add iu₁ iu₂) hB₀0]
  refine le_trans ?_ tail
  have S0 : 0 ≤ |u₁.im| + |u₂.im| := by positivity
  have wA₁ : A₁ ≤ A₀ := by rw [hA₀]; linarith
  have wA₂ : A₂ ≤ A₀ := by rw [hA₀]; linarith
  have wA₃ : A₃ ≤ A₀ := by rw [hA₀]; linarith
  have wA₄ : A₄ ≤ A₀ := by rw [hA₀]; linarith
  have wB₁ : B₁ ≤ B₀ := by rw [hB₀]; linarith
  have wB₂ : B₂ ≤ B₀ := by rw [hB₀]; linarith
  have wB₃ : B₃ ≤ B₀ := by rw [hB₀]; linarith
  have wB₄ : B₄ ≤ B₀ := by rw [hB₀]; linarith

  rcases le_or_gt (1 / 2) u₂.re with c2 | c2
  ·
    have p₂ : 0 < u₂.re := by linarith
    rw [E_of_re_pos _ _ _ _ p₂]
    rcases le_or_gt (1 / 2) u₁.re with c1 | c1
    · have p₁ : 0 < u₁.re := by linarith
      rw [E₁_of_re_pos _ _ _ p₁]
      exact weaken A₁ B₁ hA₁ wA₁ wB₁ _ _ S0 (b₁ a₁ a₂ u₁ u₂ c1 up₁ c2 up₂)
    · have l₁ : u₁.re < 1 := by linarith
      have r₁ : 1 / 2 ≤ (1 - u₁).re := by rw [Complex.sub_re, Complex.one_re]; linarith
      rw [h.E₁_of_re_lt_one a₁ a₂ l₁ p₂, norm_epsW_inv_mul]
      have := b₂ a₁ a₂ (1 - u₁) u₂ r₁ up₁' c2 up₂
      rw [im₁'] at this
      exact weaken A₂ B₂ hA₂ wA₂ wB₂ _ _ S0 this
  ·
    have l₂ : u₂.re < 1 := by linarith
    have r₂ : 1 / 2 ≤ (1 - u₂).re := by rw [Complex.sub_re, Complex.one_re]; linarith
    have p₂' : 0 < (1 - u₂).re := by linarith
    rw [h.E_of_re_lt_one a₁ a₂ u₁ l₂, norm_epsW_inv_mul]
    rcases le_or_gt (1 / 2) u₁.re with c1 | c1
    · have p₁ : 0 < u₁.re := by linarith
      rw [E₁_of_re_pos _ _ _ p₁]
      have := b₃ a₁ a₂ u₁ (1 - u₂) c1 up₁ r₂ up₂'
      rw [im₂'] at this
      exact weaken A₃ B₃ hA₃ wA₃ wB₃ _ _ S0 this
    · have l₁ : u₁.re < 1 := by linarith
      have r₁ : 1 / 2 ≤ (1 - u₁).re := by rw [Complex.sub_re, Complex.one_re]; linarith
      rw [h.F₂.E₁_of_re_lt_one a₁ a₂ l₁ p₂', norm_epsW_inv_mul]
      have := b₄ a₁ a₂ (1 - u₁) (1 - u₂) r₁ up₁' r₂ up₂'
      rw [im₁', im₂'] at this
      exact weaken A₄ B₄ hA₄ wA₄ wB₄ _ _ S0 this

end W3

end TateReal

namespace TateReal

namespace W2

open W3 LanglandsTunnell.Converse.ArchR

private def phiStd (a : ZMod 2) (v : ℝ) : ℂ :=
  (if a = 0 then 1 else (v : ℂ)) * (Real.exp (-Real.pi * v ^ 2) : ℂ)

private def psiZero (a₁ a₂ : ZMod 2) (g : Matrix (Fin 2) (Fin 2) ℝ) (x Y : ℝ) : ℂ :=
  phiStd a₁ (-(Y * g 0 0 + x * g 1 0)) * phiStd a₂ (-(Y * g 0 1 + x * g 1 1))

private theorem adm_of_det_ne_zero {g : Matrix (Fin 2) (Fin 2) ℝ} (hg : g.det ≠ 0) :
    Adm (g 1 0 ^ 2 + g 1 1 ^ 2) (g 0 0 ^ 2 + g 0 1 ^ 2) (-(g 0 0 * g 1 0 + g 0 1 * g 1 1)) 0 := by
  rw [Matrix.det_fin_two] at hg
  have hsq : 0 < (g 0 0 * g 1 1 - g 0 1 * g 1 0) ^ 2 := by positivity
  refine ⟨?_, ?_, by ring, ?_⟩
  · by_contra h
    have h10 : g 1 0 = 0 := by nlinarith [sq_nonneg (g 1 0), sq_nonneg (g 1 1)]
    have h11 : g 1 1 = 0 := by nlinarith [sq_nonneg (g 1 0), sq_nonneg (g 1 1)]
    exact hg (by rw [h10, h11]; ring)
  · by_contra h
    have h00 : g 0 0 = 0 := by nlinarith [sq_nonneg (g 0 0), sq_nonneg (g 0 1)]
    have h01 : g 0 1 = 0 := by nlinarith [sq_nonneg (g 0 0), sq_nonneg (g 0 1)]
    exact hg (by rw [h00, h01]; ring)
  ·
    nlinarith [hsq]

private theorem gauss_part_eq (g : Matrix (Fin 2) (Fin 2) ℝ) (x Y : ℝ) :
    (Real.exp (-Real.pi * (-(Y * g 0 0 + x * g 1 0)) ^ 2) : ℂ)
        * (Real.exp (-Real.pi * (-(Y * g 0 1 + x * g 1 1)) ^ 2) : ℂ)
      = gen (g 1 0 ^ 2 + g 1 1 ^ 2) (g 0 0 ^ 2 + g 0 1 ^ 2) (-(g 0 0 * g 1 0 + g 0 1 * g 1 1)) 0 0 0 x Y := by
  unfold gen gexp
  rw [← Complex.ofReal_mul, ← Real.exp_add, Complex.ofReal_exp]
  congr 1
  push_cast
  ring

private theorem Cls.linear_mul {Ψ : ℝ → ℝ → ℂ} (h : Cls Ψ) (p q : ℝ) :
    Cls (fun x t : ℝ => ((p * x + q * t : ℝ) : ℂ) * Ψ x t) := by
  refine Cls.congr (Cls.add (Cls.smul (p : ℂ) (Cls.mulX h)) (Cls.smul (q : ℂ) (Cls.mulT h))) ?_
  funext x t
  push_cast
  ring

private theorem cls_psiZero (a₁ a₂ : ZMod 2) {g : Matrix (Fin 2) (Fin 2) ℝ} (hg : g.det ≠ 0)
    : Cls (psiZero a₁ a₂ g) := by
  have hgen := Cls.gen (0 : ℂ) (0 : ℂ) (adm_of_det_ne_zero hg)

  have key : ∀ x Y : ℝ, psiZero a₁ a₂ g x Y
      = (if a₁ = 0 then 1 else ((-g 1 0 * x + -g 0 0 * Y : ℝ) : ℂ))
        * ((if a₂ = 0 then 1 else ((-g 1 1 * x + -g 0 1 * Y : ℝ) : ℂ))
        * gen (g 1 0 ^ 2 + g 1 1 ^ 2) (g 0 0 ^ 2 + g 0 1 ^ 2) (-(g 0 0 * g 1 0 + g 0 1 * g 1 1)) 0 0 0 x Y) := by
    intro x Y
    unfold psiZero phiStd
    rw [← gauss_part_eq]
    split_ifs <;> push_cast <;> ring
  by_cases h₁ : a₁ = 0 <;> by_cases h₂ : a₂ = 0
  · refine Cls.congr hgen ?_; funext x Y; rw [key]; simp [h₁, h₂]
  · refine Cls.congr (Cls.linear_mul hgen (-g 1 1) (-g 0 1)) ?_; funext x Y; rw [key]; simp [h₁, h₂]
  · refine Cls.congr (Cls.linear_mul hgen (-g 1 0) (-g 0 0)) ?_; funext x Y; rw [key]; simp [h₁, h₂]
  · refine Cls.congr (Cls.linear_mul (Cls.linear_mul hgen (-g 1 1) (-g 0 1)) (-g 1 0) (-g 0 0)) ?_
    funext x Y; rw [key]; simp [h₁, h₂]

private def innerW (a₁ a₂ : ZMod 2) (h : Matrix (Fin 2) (Fin 2) ℝ) (t : ℝ) : ℂ :=
  ∫ x : ℝ, phiStd a₁ (-(t * (h 0 0 + x * h 1 0))) * phiStd a₂ (-(t * (h 0 1 + x * h 1 1))) * psi (-x)

private def _root_.TateReal.W2.Wmem (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2) (g : Matrix (Fin 2) (Fin 2) ℝ) : ℂ :=
  ((|g.det| : ℝ) : ℂ) * quasiChar u₁ a₁ g.det * ∫ t : ℝ, innerW a₁ a₂ g t * quasiChar (u₁ - u₂) (a₁ + a₂) t

p2m_export "TateReal.W2" "Wmem"
private theorem diagOne_mul_entries (y : ℝ) (g : Matrix (Fin 2) (Fin 2) ℝ) :
    (diagOne y * g) 0 0 = y * g 0 0 ∧ (diagOne y * g) 0 1 = y * g 0 1 ∧ (diagOne y * g) 1 0 = g 1 0 ∧
      (diagOne y * g) 1 1 = g 1 1 := by
  simp [diagOne, Matrix.mul_apply, Fin.sum_univ_two]

private theorem det_diagOne_mul (y : ℝ) (g : Matrix (Fin 2) (Fin 2) ℝ) : (diagOne y * g).det = y * g.det := by
  rw [Matrix.det_mul]; simp [diagOne, Matrix.det_fin_two_of]

private theorem innerW_diagOne (a₁ a₂ : ZMod 2) (g : Matrix (Fin 2) (Fin 2) ℝ) {t : ℝ} (ht : t ≠ 0) (y : ℝ) :
    innerW a₁ a₂ (diagOne y * g) t = ((|t|⁻¹ : ℝ) : ℂ) * F₁ (psiZero a₁ a₂ g) t⁻¹ (t * y) := by
  obtain ⟨h00, h01, h10, h11⟩ := diagOne_mul_entries y g
  unfold innerW F₁
  rw [Real.fourier_eq']

  have hsub := Measure.integral_comp_mul_left
    (fun v : ℝ => cexp (((-2 * Real.pi * (inner ℝ v t⁻¹ : ℝ) : ℝ) : ℂ) * I) • psiZero a₁ a₂ g v (t * y)) t
  have hpt : ∀ x : ℝ, phiStd a₁ (-(t * ((diagOne y * g) 0 0 + x * (diagOne y * g) 1 0)))
        * phiStd a₂ (-(t * ((diagOne y * g) 0 1 + x * (diagOne y * g) 1 1))) * psi (-x)
      = cexp (((-2 * Real.pi * (inner ℝ (t * x) t⁻¹ : ℝ) : ℝ) : ℂ) * I)
          • psiZero a₁ a₂ g (t * x) (t * y) := by
    intro x
    have hin : (inner ℝ (t * x) t⁻¹ : ℝ) = t⁻¹ * (t * x) := rfl
    rw [h00, h01, h10, h11, hin, smul_eq_mul, psiZero, psi, mul_comm,
      show -(t * (y * g 0 0 + x * g 1 0)) = -(t * y * g 0 0 + t * x * g 1 0) by ring,
      show -(t * (y * g 0 1 + x * g 1 1)) = -(t * y * g 0 1 + t * x * g 1 1) by ring]
    have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht
    congr 2
    push_cast
    field_simp
  calc (∫ x : ℝ, phiStd a₁ (-(t * ((diagOne y * g) 0 0 + x * (diagOne y * g) 1 0)))
          * phiStd a₂ (-(t * ((diagOne y * g) 0 1 + x * (diagOne y * g) 1 1))) * psi (-x))
      = ∫ x : ℝ, cexp (((-2 * Real.pi * (inner ℝ (t * x) t⁻¹ : ℝ) : ℝ) : ℂ) * I)
            • psiZero a₁ a₂ g (t * x) (t * y) :=
        integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = ((|t|⁻¹ : ℝ) : ℂ) * ∫ v : ℝ, cexp (((-2 * Real.pi * (inner ℝ v t⁻¹ : ℝ) : ℝ) : ℂ) * I)
            • psiZero a₁ a₂ g v (t * y) := by
        rw [hsub, abs_inv]
        exact Complex.real_smul

section

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem rpow_weight_eq {x : ℝ} (hx : 0 < x) (H : ℝ → E) :
    (|(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1)) • H (x ^ (-1 : ℝ)) = ((x ^ 2)⁻¹ : ℝ) • H x⁻¹ := by
  rw [Real.rpow_neg_one, abs_neg, abs_one, one_mul, show (-1 : ℝ) - 1 = -((2 : ℕ) : ℝ) by norm_num,
    Real.rpow_neg hx.le, Real.rpow_natCast]

private theorem integral_Ioi_comp_inv (H : ℝ → E) :
    ∫ y in Ioi (0 : ℝ), H y = ∫ x in Ioi (0 : ℝ), ((x ^ 2)⁻¹ : ℝ) • H x⁻¹ := by
  rw [← integral_comp_rpow_Ioi H (p := -1) (by norm_num)]
  exact setIntegral_congr_fun measurableSet_Ioi fun x hx => rpow_weight_eq hx H

private theorem integrableOn_Ioi_comp_inv {H : ℝ → E} (hH : IntegrableOn H (Ioi 0)) :
    IntegrableOn (fun x : ℝ => ((x ^ 2)⁻¹ : ℝ) • H x⁻¹) (Ioi 0) := by
  have := (integrableOn_Ioi_comp_rpow_iff H (p := -1) (by norm_num)).mpr hH
  exact this.congr_fun (fun x hx => rpow_weight_eq hx H) measurableSet_Ioi

private theorem integrable_comp_inv_real {H : ℝ → E} (hH : Integrable H) :
    Integrable fun τ : ℝ => ((τ ^ 2)⁻¹ : ℝ) • H τ⁻¹ := by
  set K : ℝ → E := fun τ => ((τ ^ 2)⁻¹ : ℝ) • H τ⁻¹ with hK_def
  have hKneg : ∀ x : ℝ, K (-x) = ((x ^ 2)⁻¹ : ℝ) • H (-x⁻¹) := by
    intro x; simp only [hK_def, neg_sq, inv_neg]
  have hK_pos : IntegrableOn K (Ioi 0) := integrableOn_Ioi_comp_inv hH.integrableOn
  have hK_neg : IntegrableOn K (Iic 0) := by
    have h1 : IntegrableOn (fun x : ℝ => K (-x)) (Ioi 0) := by
      have := integrableOn_Ioi_comp_inv (H := fun t => H (-t)) hH.comp_neg.integrableOn
      exact this.congr_fun (fun x _ => (hKneg x).symm) measurableSet_Ioi
    have h1' : IntegrableOn (fun x : ℝ => K (-x)) (Ici 0) := (integrableOn_Ici_iff_integrableOn_Ioi).mpr h1
    have h2 : Integrable ((Ici (0 : ℝ)).indicator fun x => K (-x)) :=
      (integrable_indicator_iff measurableSet_Ici).mpr h1'
    have h3 := h2.comp_neg
    rw [← integrable_indicator_iff measurableSet_Iic]
    refine h3.congr (Filter.Eventually.of_forall fun τ => ?_)
    simp only [indicator_apply, mem_Ici, mem_Iic, neg_neg, neg_nonneg]
  have := hK_neg.union hK_pos
  rw [Iic_union_Ioi] at this
  exact integrableOn_univ.mp this

private theorem integral_comp_inv_real (H : ℝ → E) (hH : Integrable H) :
    ∫ t : ℝ, H t = ∫ τ : ℝ, ((τ ^ 2)⁻¹ : ℝ) • H τ⁻¹ := by
  set K : ℝ → E := fun τ => ((τ ^ 2)⁻¹ : ℝ) • H τ⁻¹ with hK_def
  have hKneg : ∀ x : ℝ, K (-x) = ((x ^ 2)⁻¹ : ℝ) • H (-x⁻¹) := by
    intro x; simp only [hK_def, neg_sq, inv_neg]
  have hK : Integrable K := integrable_comp_inv_real hH
  have hneg_split : ∫ t in Iic (0 : ℝ), H t = ∫ x in Ioi (0 : ℝ), H (-x) := by
    have := integral_comp_neg_Ioi (0 : ℝ) H; rw [neg_zero] at this; exact this.symm
  have hneg_splitK : ∫ τ in Iic (0 : ℝ), K τ = ∫ x in Ioi (0 : ℝ), K (-x) := by
    have := integral_comp_neg_Ioi (0 : ℝ) K; rw [neg_zero] at this; exact this.symm
  calc ∫ t : ℝ, H t
      = (∫ t in Ioi (0 : ℝ), H t) + ∫ t in Iic (0 : ℝ), H t := by
        rw [← integral_add_compl measurableSet_Ioi hH, compl_Ioi]
    _ = (∫ τ in Ioi (0 : ℝ), K τ) + ∫ τ in Iic (0 : ℝ), K τ := by
        congr 1
        · exact integral_Ioi_comp_inv H
        · rw [hneg_split, hneg_splitK, integral_Ioi_comp_inv (fun x => H (-x))]
          exact setIntegral_congr_fun measurableSet_Ioi fun x _ => (hKneg x).symm
    _ = ∫ τ : ℝ, K τ := by
        rw [← integral_add_compl measurableSet_Ioi hK, compl_Ioi]

end

section Kernel

private theorem quasiChar_eq (u : ℂ) (a : ZMod 2) (y : ℝ) : quasiChar u a y = ((|y| : ℝ) : ℂ) ^ u * sgnPow a y := rfl

private theorem sgnPow_mul (a : ZMod 2) (y z : ℝ) : sgnPow a (y * z) = sgnPow a y * sgnPow a z := by
  unfold sgnPow
  split_ifs
  · ring
  · rw [sign_mul]; push_cast; ring

private theorem sgnPow_inv (a : ZMod 2) (y : ℝ) : sgnPow a y⁻¹ = sgnPow a y := by
  unfold sgnPow
  split_ifs
  · rfl
  · rcases lt_trichotomy y 0 with h | rfl | h
    · rw [sign_neg h, sign_neg (inv_lt_zero.mpr h)]
    · simp
    · rw [sign_pos h, sign_pos (inv_pos.mpr h)]

private theorem sgnPow_sq {y : ℝ} (hy : y ≠ 0) (a : ZMod 2) : sgnPow a y * sgnPow a y = 1 := by
  unfold sgnPow
  split_ifs
  · ring
  · rcases hy.lt_or_gt with h | h
    · simp [sign_neg h]
    · simp [sign_pos h]

private theorem sgnPow_add {y : ℝ} (hy : y ≠ 0) (a b : ZMod 2) : sgnPow (a + b) y = sgnPow a y * sgnPow b y := by
  have hsum : ∀ a b : ZMod 2, a ≠ 0 → b ≠ 0 → a + b = 0 := by decide
  by_cases ha : a = 0
  · subst ha; simp [sgnPow]
  by_cases hb : b = 0
  · subst hb; simp [sgnPow]
  rw [hsum a b ha hb]
  have h1 := sgnPow_sq hy a
  simp only [sgnPow, ha, hb, if_false, if_true] at h1 ⊢
  exact h1.symm

private theorem ker_mul (b : ZMod 2) (w : ℂ) (y z : ℝ) : ker b w (y * z) = ker b w y * ker b w z := by
  unfold ker
  rw [abs_mul, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (abs_nonneg y) (abs_nonneg z), sgnPow_mul]
  ring

private theorem kernel_y {y : ℝ} (hy : y ≠ 0) (u₁ u : ℂ) (a₁ a : ZMod 2) (s : ℂ) :
    ((|y| : ℝ) : ℂ) * quasiChar u₁ a₁ y * quasiChar u a y * ((|y| : ℝ) : ℂ) ^ (s - 1) * ((|y| : ℝ) : ℂ)⁻¹
      = ker (a + a₁) (s + u + u₁) y := by
  have hX : ((|y| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (abs_pos.mpr hy).ne'
  rw [quasiChar_eq, quasiChar_eq, ker, sgnPow_add hy, show s + u + u₁ - 1 = u₁ + u + (s - 1) by ring,
    cpow_add _ _ hX, cpow_add _ _ hX]
  field_simp

private theorem kernel_tau {τ : ℝ} (hτ : τ ≠ 0) (u₁ u₂ u : ℂ) (a₁ a₂ a : ZMod 2) (s : ℂ) :
    quasiChar (u₁ - u₂) (a₁ + a₂) τ⁻¹ * ker (a + a₁) (s + u + u₁) τ = ker (a + a₂) (s + u + u₂) τ := by
  have hX : ((|τ| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (abs_pos.mpr hτ).ne'
  have harg : ((|τ| : ℝ) : ℂ).arg ≠ Real.pi := by
    rw [arg_ofReal_of_nonneg (abs_nonneg τ)]; exact Real.pi_pos.ne
  rw [quasiChar_eq, ker, ker, abs_inv, Complex.ofReal_inv, inv_cpow _ _ harg, sgnPow_inv,
    sgnPow_add hτ a a₁, sgnPow_add hτ a₁ a₂, sgnPow_add hτ a a₂,
    show s + u + u₂ - 1 = (s + u + u₁ - 1) - (u₁ - u₂) by ring, cpow_sub (s + u + u₁ - 1) (u₁ - u₂) hX,
    div_eq_mul_inv]
  have h1 := sgnPow_sq hτ a₁
  linear_combination (sgnPow a τ * sgnPow a₂ τ * ((|τ| : ℝ) : ℂ) ^ (s + u + u₁ - 1)
    * (((|τ| : ℝ) : ℂ) ^ (u₁ - u₂))⁻¹) * h1

end Kernel

section Bridge

private theorem quasiChar_mul' (u : ℂ) (a : ZMod 2) (y z : ℝ) : quasiChar u a (y * z)
    = quasiChar u a y * quasiChar u a z := by
  rw [quasiChar_eq, quasiChar_eq, quasiChar_eq, abs_mul, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (abs_nonneg y) (abs_nonneg z), sgnPow_mul]
  ring

private theorem InSpan.integrable_mul_ker {f : ℝ → ℂ} (h : InSpan f) (b : ZMod 2) {w : ℂ} (hw : 0 < w.re) :
    Integrable fun x : ℝ => f x * ker b w x := by
  induction h with
  | mem hf =>
    have := hf.integrable_tate b hw
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [ker]; ring
  | smul c _ ih =>
    refine (ih.const_mul c).congr (Filter.Eventually.of_forall fun x => ?_)
    simp only; ring
  | add _ _ ih₁ ih₂ =>
    refine (ih₁.add ih₂).congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply]; ring

private theorem measurable_quasiChar (u : ℂ) (a : ZMod 2) : Measurable (quasiChar u a) := by
  have : quasiChar u a = fun y : ℝ => ((|y| : ℝ) : ℂ) ^ u * sgnPow a y := funext fun y => quasiChar_eq u a y
  rw [this]
  exact ((Complex.measurable_ofReal.comp measurable_abs).pow_const u).mul (measurable_sgnPow a)

private def Psi (a₁ a₂ : ZMod 2) (g : Matrix (Fin 2) (Fin 2) ℝ) : ℝ → ℝ → ℂ := fun Y τ => F₁ (psiZero a₁ a₂ g) τ Y

private theorem cls_Psi (a₁ a₂ : ZMod 2) {g : Matrix (Fin 2) (Fin 2) ℝ} (hg : g.det ≠ 0) : Cls (Psi a₁ a₂ g) :=
  (cls_psiZero a₁ a₂ hg).F₁.swap

private def G (u₁ u₂ u : ℂ) (a₁ a₂ a : ZMod 2) (s : ℂ) (g : Matrix (Fin 2) (Fin 2) ℝ) (y t : ℝ) : ℂ :=
  ker (a + a₁) (s + u + u₁) y
    * ((((|t|⁻¹ : ℝ) : ℂ) * F₁ (psiZero a₁ a₂ g) t⁻¹ (t * y)) * quasiChar (u₁ - u₂) (a₁ + a₂) t)

private def Kt (u₁ u₂ u : ℂ) (a₁ a₂ a : ZMod 2) (s : ℂ) (t : ℝ) : ℂ :=
  ((|t|⁻¹ : ℝ) : ℂ) * quasiChar (u₁ - u₂) (a₁ + a₂) t * ker (a + a₁) (s + u + u₁) t⁻¹

private def inner' (u₁ u : ℂ) (a₁ a₂ a : ZMod 2) (s : ℂ) (g : Matrix (Fin 2) (Fin 2) ℝ) (τ : ℝ) : ℂ :=
  ∫ Y : ℝ, F₁ (psiZero a₁ a₂ g) τ Y * ker (a + a₁) (s + u + u₁) Y

variable (u₁ u₂ u : ℂ) (a₁ a₂ a : ZMod 2) (s : ℂ) (g : Matrix (Fin 2) (Fin 2) ℝ)

private theorem G_eq {t : ℝ} (ht : t ≠ 0) (y : ℝ) :
    G u₁ u₂ u a₁ a₂ a s g y t
      = Kt u₁ u₂ u a₁ a₂ a s t
          * (F₁ (psiZero a₁ a₂ g) t⁻¹ (t * y) * ker (a + a₁) (s + u + u₁) (t * y)) := by
  unfold G Kt
  have hk : ker (a + a₁) (s + u + u₁) y = ker (a + a₁) (s + u + u₁) t⁻¹ * ker (a + a₁) (s + u + u₁) (t * y) := by
    rw [← ker_mul, inv_mul_cancel_left₀ ht]
  rw [hk]
  ring

private theorem integral_cmul (r : ℂ) (f : ℝ → ℂ) : ∫ x : ℝ, r * f x = r * ∫ x : ℝ, f x := integral_const_mul r f

private theorem integral_rmul (r : ℝ) (f : ℝ → ℝ) : ∫ x : ℝ, r * f x = r * ∫ x : ℝ, f x := integral_const_mul r f

private theorem integral_G {t : ℝ} (ht : t ≠ 0) :
    ∫ y : ℝ, G u₁ u₂ u a₁ a₂ a s g y t
      = Kt u₁ u₂ u a₁ a₂ a s t * (((|t|⁻¹ : ℝ) : ℂ) * inner' u₁ u a₁ a₂ a s g t⁻¹) := by
  simp_rw [G_eq u₁ u₂ u a₁ a₂ a s g ht]
  rw [integral_cmul]
  congr 1
  unfold inner'
  rw [Measure.integral_comp_mul_left
    (fun Y : ℝ => F₁ (psiZero a₁ a₂ g) t⁻¹ Y * ker (a + a₁) (s + u + u₁) Y) t, abs_inv]
  exact Complex.real_smul

private theorem integral_norm_G {t : ℝ} (ht : t ≠ 0) :
    ∫ y : ℝ, ‖G u₁ u₂ u a₁ a₂ a s g y t‖
      = ‖Kt u₁ u₂ u a₁ a₂ a s t‖ * (|t|⁻¹
          * ∫ Y : ℝ, ‖F₁ (psiZero a₁ a₂ g) t⁻¹ Y * ker (a + a₁) (s + u + u₁) Y‖) := by
  have hpt : ∀ y : ℝ, ‖G u₁ u₂ u a₁ a₂ a s g y t‖ = ‖Kt u₁ u₂ u a₁ a₂ a s t‖
      * ‖F₁ (psiZero a₁ a₂ g) t⁻¹ (t * y) * ker (a + a₁) (s + u + u₁) (t * y)‖ := fun y => by
    rw [G_eq u₁ u₂ u a₁ a₂ a s g ht, norm_mul]
  simp_rw [hpt]
  rw [integral_rmul]
  congr 1
  rw [Measure.integral_comp_mul_left
    (fun Y : ℝ => ‖F₁ (psiZero a₁ a₂ g) t⁻¹ Y * ker (a + a₁) (s + u + u₁) Y‖) t, abs_inv, smul_eq_mul]

private theorem measurable_uncurry_G (hg : g.det ≠ 0) : Measurable (Function.uncurry (G u₁ u₂ u a₁ a₂ a s g)) := by
  have hF : Continuous fun p : ℝ × ℝ => F₁ (psiZero a₁ a₂ g) p.1 p.2 := (cls_psiZero a₁ a₂ hg).F₁.continuous
  have h1 : Measurable fun p : ℝ × ℝ => ker (a + a₁) (s + u + u₁) p.1 := (measurable_ker _ _).comp measurable_fst
  have h2 : Measurable fun p : ℝ × ℝ => ((|p.2|⁻¹ : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp ((measurable_abs.comp measurable_snd).inv)
  have hm : Measurable fun p : ℝ × ℝ => (p.2⁻¹, p.2 * p.1) :=
    (measurable_snd.inv).prodMk (measurable_snd.mul measurable_fst)
  have h3' := hF.measurable.comp hm
  have h3 : Measurable fun p : ℝ × ℝ => F₁ (psiZero a₁ a₂ g) p.2⁻¹ (p.2 * p.1) := h3'
  have h4 : Measurable fun p : ℝ × ℝ => quasiChar (u₁ - u₂) (a₁ + a₂) p.2 :=
    (measurable_quasiChar _ _).comp measurable_snd
  have key : Function.uncurry (G u₁ u₂ u a₁ a₂ a s g) = fun p : ℝ × ℝ => ker (a + a₁) (s + u + u₁) p.1
      * ((((|p.2|⁻¹ : ℝ) : ℂ) * F₁ (psiZero a₁ a₂ g) p.2⁻¹ (p.2 * p.1)) * quasiChar (u₁ - u₂) (a₁ + a₂) p.2) :=
    funext fun p => rfl
  rw [key]
  exact h1.mul ((h2.mul h3).mul h4)

private theorem integrable_slice_ker (hg : g.det ≠ 0) (h₁ : 0 < (s + u + u₁).re) (τ : ℝ) :
    Integrable fun Y : ℝ => F₁ (psiZero a₁ a₂ g) τ Y * ker (a + a₁) (s + u + u₁) Y :=
  InSpan.integrable_mul_ker ((cls_psiZero a₁ a₂ hg).F₁.sliceT τ) (a + a₁) h₁

private theorem ae_ne_zero : ∀ᵐ t : ℝ, t ≠ 0 := by
  filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ))] with t ht
  exact ht

private def Mprof (τ : ℝ) : ℝ :=
  ‖quasiChar (u₁ - u₂) (a₁ + a₂) τ⁻¹‖ * (‖ker (a + a₁) (s + u + u₁) τ‖
    * ∫ Y : ℝ, ‖F₁ (psiZero a₁ a₂ g) τ Y * ker (a + a₁) (s + u + u₁) Y‖)

private theorem integral_mulr (f : ℝ → ℝ) (r : ℝ) : ∫ x : ℝ, f x * r = (∫ x : ℝ, f x) * r := integral_mul_const r f

private theorem integrable_Mprof (hg : g.det ≠ 0) (h₁ : 0 < (s + u + u₁).re) (h₂ : 0 < (s + u + u₂).re) :
    Integrable (Mprof u₁ u₂ u a₁ a₂ a s g) := by
  have hz := (cls_Psi a₁ a₂ hg).integrable_zint (a + a₁) (a + a₂) h₁ h₂
  have hprod := ((integrable_prod_iff' ((cls_Psi a₁ a₂ hg).aestronglyMeasurable_zint _ _ _ _)).1 hz).2
  refine hprod.congr ?_
  filter_upwards [ae_ne_zero] with τ hτ
  unfold Mprof
  have hk : ‖quasiChar (u₁ - u₂) (a₁ + a₂) τ⁻¹‖ * ‖ker (a + a₁) (s + u + u₁) τ‖ = ‖ker (a + a₂) (s + u + u₂) τ‖ := by
    rw [← norm_mul, kernel_tau hτ]
  have hpt : ∀ Y : ℝ, ‖zint (Psi a₁ a₂ g) (a + a₁) (a + a₂) (s + u + u₁) (s + u + u₂) (Y, τ)‖
      = ‖F₁ (psiZero a₁ a₂ g) τ Y * ker (a + a₁) (s + u + u₁) Y‖ * ‖ker (a + a₂) (s + u + u₂) τ‖ := fun Y => by
    rw [zint, norm_mul]; rfl
  simp_rw [hpt]
  rw [integral_mulr, ← mul_assoc, hk, mul_comm]

private theorem integrable_uncurry_G (hg : g.det ≠ 0) (h₁ : 0 < (s + u + u₁).re) (h₂ : 0 < (s + u + u₂).re) :
    Integrable (Function.uncurry (G u₁ u₂ u a₁ a₂ a s g)) ((volume : Measure ℝ).prod volume) := by
  refine (integrable_prod_iff' (measurable_uncurry_G u₁ u₂ u a₁ a₂ a s g hg).aestronglyMeasurable).2 ⟨?_, ?_⟩
  · filter_upwards [ae_ne_zero] with t ht
    have hΦ := ((integrable_slice_ker u₁ u a₁ a₂ a s g hg h₁ t⁻¹).comp_mul_left' ht).const_mul
      (Kt u₁ u₂ u a₁ a₂ a s t)
    refine hΦ.congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [Function.uncurry_apply_pair]
    exact (G_eq u₁ u₂ u a₁ a₂ a s g ht y).symm
  · have hM := integrable_comp_inv_real (integrable_Mprof u₁ u₂ u a₁ a₂ a s g hg h₁ h₂)
    refine hM.congr ?_
    filter_upwards [ae_ne_zero] with t ht
    simp only [Function.uncurry_apply_pair]
    rw [integral_norm_G u₁ u₂ u a₁ a₂ a s g ht]
    unfold Mprof Kt
    rw [inv_inv, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_abs, smul_eq_mul]
    have : (t ^ 2)⁻¹ = |t|⁻¹ * |t|⁻¹ := by rw [← mul_inv, ← sq, sq_abs]
    rw [this]
    ring

private theorem integral_zetaIntegrand_eq :
    ∫ y : ℝ, zetaIntegrand (Wmem u₁ u₂ a₁ a₂) g u a s y
      = (((|g.det| : ℝ) : ℂ) * quasiChar u₁ a₁ g.det) * ∫ y : ℝ, ∫ t : ℝ, G u₁ u₂ u a₁ a₂ a s g y t := by
  rw [← integral_cmul]
  refine integral_congr_ae ?_
  filter_upwards [ae_ne_zero] with y hy
  unfold zetaIntegrand Wmem
  rw [det_diagOne_mul, abs_mul, Complex.ofReal_mul, quasiChar_mul']
  have hin : (∫ t : ℝ, innerW a₁ a₂ (diagOne y * g) t * quasiChar (u₁ - u₂) (a₁ + a₂) t)
      = ∫ t : ℝ, (((|t|⁻¹ : ℝ) : ℂ) * F₁ (psiZero a₁ a₂ g) t⁻¹ (t * y)) * quasiChar (u₁ - u₂) (a₁ + a₂) t := by
    refine integral_congr_ae ?_
    filter_upwards [ae_ne_zero] with t ht
    rw [innerW_diagOne a₁ a₂ g ht y]
  have hG : (∫ t : ℝ, G u₁ u₂ u a₁ a₂ a s g y t)
      = ker (a + a₁) (s + u + u₁) y
          * ∫ t : ℝ, (((|t|⁻¹ : ℝ) : ℂ) * F₁ (psiZero a₁ a₂ g) t⁻¹ (t * y)) * quasiChar (u₁ - u₂) (a₁ + a₂) t := by
    unfold G; rw [integral_cmul]
  rw [hin, hG, ← kernel_y hy u₁ u a₁ a s]
  ring

private theorem bridge (hg : g.det ≠ 0) (h₁ : 0 < (s + u + u₁).re) (h₂ : 0 < (s + u + u₂).re) :
    ∫ y : ℝ, zetaIntegrand (Wmem u₁ u₂ a₁ a₂) g u a s y
      = (((|g.det| : ℝ) : ℂ) * quasiChar u₁ a₁ g.det)
          * Z (Psi a₁ a₂ g) (a + a₁) (a + a₂) (s + u + u₁) (s + u + u₂) := by
  rw [integral_zetaIntegrand_eq u₁ u₂ u a₁ a₂ a s g,
    integral_integral_swap (integrable_uncurry_G u₁ u₂ u a₁ a₂ a s g hg h₁ h₂),
    (cls_Psi a₁ a₂ hg).Z_eq_iterated (a + a₁) (a + a₂) h₁ h₂]
  congr 1

  set H : ℝ → ℂ := fun t => Kt u₁ u₂ u a₁ a₂ a s t * (((|t|⁻¹ : ℝ) : ℂ) * inner' u₁ u a₁ a₂ a s g t⁻¹) with hH
  have hGt : (∫ t : ℝ, ∫ y : ℝ, G u₁ u₂ u a₁ a₂ a s g y t) = ∫ t : ℝ, H t := by
    refine integral_congr_ae ?_
    filter_upwards [ae_ne_zero] with t ht
    exact integral_G u₁ u₂ u a₁ a₂ a s g ht
  have hHint : Integrable H := by
    have h0 := (integrable_uncurry_G u₁ u₂ u a₁ a₂ a s g hg h₁ h₂).integral_prod_right
    refine h0.congr ?_
    filter_upwards [ae_ne_zero] with t ht
    simp only [Function.uncurry_apply_pair]
    exact integral_G u₁ u₂ u a₁ a₂ a s g ht
  rw [hGt, integral_comp_inv_real H hHint]
  refine integral_congr_ae ?_
  filter_upwards [ae_ne_zero] with τ hτ
  have hτ' : τ⁻¹ ≠ 0 := inv_ne_zero hτ
  refine (Complex.real_smul).trans ?_
  rw [hH]
  simp only
  unfold Kt
  simp only [inv_inv, abs_inv]

  have hinner : inner' u₁ u a₁ a₂ a s g τ = tateZeta (fun Y => Psi a₁ a₂ g Y τ) (a + a₁) (s + u + u₁) := by
    rw [tateZeta_eq_integral_ker]; rfl
  rw [hinner, ← kernel_tau hτ u₁ u₂ u a₁ a₂ a s]
  have habs : ((|τ| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (abs_pos.mpr hτ).ne'
  have hsq : (((τ ^ 2)⁻¹ : ℝ) : ℂ) = (((|τ| : ℝ) : ℂ) * ((|τ| : ℝ) : ℂ))⁻¹ := by
    have h : (τ ^ 2)⁻¹ = (|τ| * |τ|)⁻¹ := by rw [← sq, sq_abs]
    rw [h]; push_cast; ring
  rw [hsq]
  field_simp

end Bridge

end W2

end TateReal

end

set_option autoImplicit false

open Complex MeasureTheory LanglandsTunnell

noncomputable section

namespace TateReal
namespace W2C

private theorem archFactor_twist_principal (u₁ u₂ u s : ℂ) (a₁ a₂ a : ZMod 2) :
    ((RealArchParam.principal u₁ a₁ u₂ a₂).twist u a).archFactor s
      = Gammaℝ (s + (u₁ + u + signShift (a₁ + a))) * Gammaℝ (s + (u₂ + u + signShift (a₂ + a))) := by
  simp [RealArchParam.twist, RealArchParam.archFactor, RealArchParam.gammaR, RealArchParam.gammaC]

private theorem archFactor_twist_principal' (u₁ u₂ u s : ℂ) (a₁ a₂ a : ZMod 2) :
    ((RealArchParam.principal u₁ a₁ u₂ a₂).twist u a).archFactor s
      = Gammaℝ (s + u + u₁ + signShift (a + a₁)) * Gammaℝ (s + u + u₂ + signShift (a + a₂)) := by
  rw [archFactor_twist_principal, add_comm a a₁, add_comm a a₂]
  congr 1 <;> congr 1 <;> ring

private theorem epsilonFactor_twist_principal (u₁ u₂ u : ℂ) (a₁ a₂ a : ZMod 2) :
    ((RealArchParam.principal u₁ a₁ u₂ a₂).twist u a).epsilonFactor
      = signEpsilon (a + a₁) * signEpsilon (a + a₂) := by
  rw [show (RealArchParam.principal u₁ a₁ u₂ a₂).twist u a
      = RealArchParam.principal (u₁ + u) (a₁ + a) (u₂ + u) (a₂ + a) from rfl,
    RealArchParam.epsilonFactor_principal, add_comm a₁ a, add_comm a₂ a]

private theorem neg_one_pow_mul_neg_I_pow (b : ZMod 2) :
    (-1 : ℂ) ^ (if b = 0 then 0 else 1 : ℕ) * (-I) ^ (if b = 0 then 0 else 1 : ℕ) = signEpsilon b := by
  by_cases hb : b = 0 <;> simp [signEpsilon, hb]

private theorem neg_I_pow_inv (b : ZMod 2) :
    ((-I) ^ (if b = 0 then 0 else 1 : ℕ))⁻¹ = signEpsilon b := by
  by_cases hb : b = 0 <;> simp [signEpsilon, hb, inv_neg, Complex.inv_I]

private theorem centralExponent_principal (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2) :
    (RealArchParam.principal u₁ a₁ u₂ a₂).centralExponent = u₁ + u₂ := rfl

private theorem centralSign_principal (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2) :
    (RealArchParam.principal u₁ a₁ u₂ a₂).centralSign = a₁ + a₂ := rfl

private theorem zmod_two_add_add_add_left (x y z : ZMod 2) : x + (y + z) + y = x + z := by
  revert x y z; decide

private theorem zmod_two_add_add_add_right (x y z : ZMod 2) : x + (y + z) + z = x + y := by
  revert x y z; decide

end TateReal.W2C

namespace TateReal

private theorem sh_eq_signShift (b : ZMod 2) : sh b = signShift b := by
  by_cases hb : b = 0 <;> simp [sh, signShift, hb]

namespace W2

open W3 W2C LanglandsTunnell.Converse.ArchR

private def zetaEnt (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2) (g : Matrix (Fin 2) (Fin 2) ℝ) (u : ℂ) (a : ZMod 2) (s : ℂ) : ℂ :=
  (((|g.det| : ℝ) : ℂ) * quasiChar u₁ a₁ g.det)
    * E (Psi a₁ a₂ g) (a + a₁) (a + a₂) (s + u + u₁) (s + u + u₂)

private theorem sgnW_mul_epsW_mul_epsW_inv (b₁ b₂ : ZMod 2) :
    sgnW b₁ * epsW b₁ * (epsW b₂)⁻¹ = signEpsilon b₁ * signEpsilon b₂ := by
  unfold sgnW epsW
  rw [neg_one_pow_mul_neg_I_pow, neg_I_pow_inv]

private theorem det_weyl : weyl.det = 1 := by
  norm_num [weyl, Matrix.det_fin_two_of]

variable (u₁ u₂ u : ℂ) (a₁ a₂ a : ZMod 2) (s : ℂ) (g : Matrix (Fin 2) (Fin 2) ℝ)

private theorem det_weyl_mul : (weyl * g).det = g.det := by
  rw [Matrix.det_mul, det_weyl, one_mul]

private theorem weyl_mul_entries :
    (weyl * g) 0 0 = g 1 0 ∧ (weyl * g) 0 1 = g 1 1 ∧ (weyl * g) 1 0 = -g 0 0 ∧ (weyl * g) 1 1 = -g 0 1 := by
  simp [weyl, Matrix.mul_apply, Fin.sum_univ_two]

private theorem psiZero_weyl_mul : psiZero a₁ a₂ (weyl * g) = fun x Y => psiZero a₁ a₂ g Y (-x) := by
  obtain ⟨h00, h01, h10, h11⟩ := weyl_mul_entries g
  funext x Y
  unfold psiZero
  rw [h00, h01, h10, h11]
  congr 1 <;> congr 1 <;> ring

private theorem E_Psi {m : Matrix (Fin 2) (Fin 2) ℝ} (hm : m.det ≠ 0) (p₁ p₂ : ZMod 2) (v₁ v₂ : ℂ) :
    E (Psi a₁ a₂ m) p₁ p₂ v₁ v₂ = epsW p₂ * E (psiZero a₁ a₂ m) p₂ p₁ (1 - v₂) v₁ := by
  have hc := cls_psiZero a₁ a₂ hm
  have h1 : E (Psi a₁ a₂ m) p₁ p₂ v₁ v₂ = E (F₁ (psiZero a₁ a₂ m)) p₂ p₁ v₂ v₁ :=
    hc.F₁.E_swap p₂ p₁ v₂ v₁
  have h2 := hc.E_F₁ p₂ p₁ (1 - v₂) v₁
  rw [sub_sub_cancel] at h2
  rw [h1, h2]

private theorem E_Psi_weyl (hg : g.det ≠ 0) (b₁ b₂ : ZMod 2) (w₁ w₂ : ℂ) :
    E (Psi a₁ a₂ (weyl * g)) b₂ b₁ (1 - w₂) (1 - w₁)
      = (sgnW b₁ * epsW b₁ * (epsW b₂)⁻¹) * E (Psi a₁ a₂ g) b₁ b₂ w₁ w₂ := by
  have hg' : (weyl * g).det ≠ 0 := by rwa [det_weyl_mul]
  have hc := cls_psiZero a₁ a₂ hg
  have hrefl : E (fun x Y => psiZero a₁ a₂ g Y (-x)) b₁ b₂ w₁ (1 - w₂)
      = sgnW b₁ * E (fun x t => psiZero a₁ a₂ g t x) b₁ b₂ w₁ (1 - w₂) :=
    hc.swap.E_reflX b₁ b₂ w₁ (1 - w₂)
  have hswap : E (fun x t => psiZero a₁ a₂ g t x) b₁ b₂ w₁ (1 - w₂)
      = E (psiZero a₁ a₂ g) b₂ b₁ (1 - w₂) w₁ :=
    hc.E_swap b₂ b₁ (1 - w₂) w₁
  rw [E_Psi a₁ a₂ hg' b₂ b₁ (1 - w₂) (1 - w₁), sub_sub_cancel, psiZero_weyl_mul, hrefl, hswap,
    E_Psi a₁ a₂ hg b₁ b₂ w₁ w₂, mul_assoc (sgnW b₁ * epsW b₁), inv_mul_cancel_left₀ (epsW_ne_zero b₂)]
  ring

private theorem re_pos_of_abscissa_lt (hs : max (-u₁.re) (-u₂.re) < s.re + u.re) :
    0 < (s + u + u₁).re ∧ 0 < (s + u + u₂).re := by
  have m₁ := le_max_left (-u₁.re) (-u₂.re)
  have m₂ := le_max_right (-u₁.re) (-u₂.re)
  simp only [Complex.add_re]
  constructor <;> linarith

private theorem zetaIntegrand_Wmem_eq {y : ℝ} (hy : y ≠ 0) :
    zetaIntegrand (Wmem u₁ u₂ a₁ a₂) g u a s y
      = (((|g.det| : ℝ) : ℂ) * quasiChar u₁ a₁ g.det) * ∫ t : ℝ, G u₁ u₂ u a₁ a₂ a s g y t := by
  unfold zetaIntegrand Wmem
  rw [det_diagOne_mul, abs_mul, Complex.ofReal_mul, quasiChar_mul']
  have hin : (∫ t : ℝ, innerW a₁ a₂ (diagOne y * g) t * quasiChar (u₁ - u₂) (a₁ + a₂) t)
      = ∫ t : ℝ, (((|t|⁻¹ : ℝ) : ℂ) * F₁ (psiZero a₁ a₂ g) t⁻¹ (t * y)) * quasiChar (u₁ - u₂) (a₁ + a₂) t := by
    refine integral_congr_ae ?_
    filter_upwards [ae_ne_zero] with t ht
    rw [innerW_diagOne a₁ a₂ g ht y]
  have hG : (∫ t : ℝ, G u₁ u₂ u a₁ a₂ a s g y t)
      = ker (a + a₁) (s + u + u₁) y
          * ∫ t : ℝ, (((|t|⁻¹ : ℝ) : ℂ) * F₁ (psiZero a₁ a₂ g) t⁻¹ (t * y)) * quasiChar (u₁ - u₂) (a₁ + a₂) t := by
    unfold G; rw [integral_cmul]
  rw [hin, hG, ← kernel_y hy u₁ u a₁ a s]
  ring

private theorem integrable_zetaIntegrand_Wmem (hg : g.det ≠ 0) (hs : max (-u₁.re) (-u₂.re) < s.re + u.re) :
    Integrable (zetaIntegrand (Wmem u₁ u₂ a₁ a₂) g u a s) := by
  obtain ⟨h₁, h₂⟩ := re_pos_of_abscissa_lt u₁ u₂ u s hs
  have hG := (integrable_uncurry_G u₁ u₂ u a₁ a₂ a s g hg h₁ h₂).integral_prod_left
  refine (hG.const_mul (((|g.det| : ℝ) : ℂ) * quasiChar u₁ a₁ g.det)).congr ?_
  filter_upwards [ae_ne_zero] with y hy
  simp only [Function.uncurry_apply_pair]
  exact (zetaIntegrand_Wmem_eq u₁ u₂ u a₁ a₂ a s g hy).symm

private theorem integral_zetaIntegrand_Wmem (hg : g.det ≠ 0) (hs : max (-u₁.re) (-u₂.re) < s.re + u.re) :
    ∫ y : ℝ, zetaIntegrand (Wmem u₁ u₂ a₁ a₂) g u a s y
      = ((RealArchParam.principal u₁ a₁ u₂ a₂).twist u a).archFactor s * zetaEnt u₁ u₂ a₁ a₂ g u a s := by
  obtain ⟨h₁, h₂⟩ := re_pos_of_abscissa_lt u₁ u₂ u s hs
  rw [bridge u₁ u₂ u a₁ a₂ a s g hg h₁ h₂, Z_eq_E (Psi a₁ a₂ g) (a + a₁) (a + a₂) h₁ h₂,
    archFactor_twist_principal']
  unfold zetaEnt
  simp only [sh_eq_signShift]
  ring

private theorem zetaEnt_differentiable : Differentiable ℂ (zetaEnt u₁ u₂ a₁ a₂ g u a) := by
  by_cases hg : g.det = 0
  · have h0 : zetaEnt u₁ u₂ a₁ a₂ g u a = fun _ => 0 := by
      funext s
      simp [zetaEnt, hg]
    rw [h0]
    exact differentiable_const 0
  · have hd : Differentiable ℂ fun s : ℂ =>
        E (Psi a₁ a₂ g) (a + a₁) (a + a₂) (s + u + u₁) (s + u + u₂) :=
      (cls_Psi a₁ a₂ hg).differentiable_E_comp (a + a₁) (a + a₂) 1 (u + u₁) 1 (u + u₂)
        (fun w => by ring) (fun w => by ring)
    show Differentiable ℂ fun s : ℂ => (((|g.det| : ℝ) : ℂ) * quasiChar u₁ a₁ g.det)
      * E (Psi a₁ a₂ g) (a + a₁) (a + a₂) (s + u + u₁) (s + u + u₂)
    exact hd.const_mul _

private theorem zetaEnt_finiteOrder (A B : ℝ) : ∃ C D : ℝ, ∀ z : ℂ, A ≤ z.re → z.re ≤ B →
    ‖zetaEnt u₁ u₂ a₁ a₂ g u a z‖ ≤ C * Real.exp (D * |z.im|) := by
  by_cases hg : g.det = 0
  · refine ⟨0, 0, fun z _ _ => ?_⟩
    simp [zetaEnt, hg]
  · obtain ⟨C, D, hCD⟩ :=
      (cls_Psi a₁ a₂ hg).exists_E_strip_bound (a + a₁) (a + a₂) (u + u₁) (u + u₂) A B
    refine ⟨‖(((|g.det| : ℝ) : ℂ) * quasiChar u₁ a₁ g.det)‖ * C, D, fun z hA hB => ?_⟩
    unfold zetaEnt
    rw [norm_mul, add_assoc z u u₁, add_assoc z u u₂, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hCD z hA hB) (norm_nonneg _)

private theorem zetaEnt_functional_equation (hg : g.det ≠ 0) :
    zetaEnt u₁ u₂ a₁ a₂ (weyl * g) (-(u + (RealArchParam.principal u₁ a₁ u₂ a₂).centralExponent))
        (a + (RealArchParam.principal u₁ a₁ u₂ a₂).centralSign) (1 - s)
      = ((RealArchParam.principal u₁ a₁ u₂ a₂).twist u a).epsilonFactor * zetaEnt u₁ u₂ a₁ a₂ g u a s := by
  rw [centralExponent_principal, centralSign_principal, epsilonFactor_twist_principal]
  unfold zetaEnt
  rw [det_weyl_mul, zmod_two_add_add_add_left, zmod_two_add_add_add_right,
    show 1 - s + -(u + (u₁ + u₂)) + u₁ = 1 - (s + u + u₂) by ring,
    show 1 - s + -(u + (u₁ + u₂)) + u₂ = 1 - (s + u + u₁) by ring,
    E_Psi_weyl a₁ a₂ g hg (a + a₁) (a + a₂) (s + u + u₁) (s + u + u₂), sgnW_mul_epsW_mul_epsW_inv]
  ring

private theorem psi_add (x y : ℝ) : psi (x + y) = psi x * psi y := by
  unfold psi; rw [← Complex.exp_add]; congr 1; push_cast; ring

private theorem quasiChar_ne_zero (u' : ℂ) (a' : ZMod 2) {y : ℝ} (hy : y ≠ 0) : quasiChar u' a' y ≠ 0 := by
  unfold quasiChar
  apply mul_ne_zero
  · have habs : ((|y| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (abs_pos.mpr hy).ne'
    rw [Complex.cpow_def_of_ne_zero habs]
    exact Complex.exp_ne_zero _
  · split_ifs
    · exact one_ne_zero
    · rcases hy.lt_or_gt with h | h
      · simp [sign_neg h]
      · simp [sign_pos h]

private theorem unip_mul_apply (x₀ : ℝ) (m : Matrix (Fin 2) (Fin 2) ℝ) :
    (unip x₀ * m) 0 0 = m 0 0 + x₀ * m 1 0 ∧ (unip x₀ * m) 0 1 = m 0 1 + x₀ * m 1 1 ∧
      (unip x₀ * m) 1 0 = m 1 0 ∧ (unip x₀ * m) 1 1 = m 1 1 := by
  simp [unip, Matrix.mul_apply, Fin.sum_univ_two]

private theorem det_unip_mul (x₀ : ℝ) (m : Matrix (Fin 2) (Fin 2) ℝ) : (unip x₀ * m).det = m.det := by
  rw [Matrix.det_mul]; simp [unip]

private theorem innerW_unip (x₀ : ℝ) (m : Matrix (Fin 2) (Fin 2) ℝ) (t : ℝ) :
    innerW a₁ a₂ (unip x₀ * m) t = psi x₀ * innerW a₁ a₂ m t := by
  unfold innerW
  obtain ⟨h00, h01, h10, h11⟩ := unip_mul_apply x₀ m
  simp only [h00, h01, h10, h11]
  set f : ℝ → ℂ := fun x =>
    phiStd a₁ (-(t * (m 0 0 + x * m 1 0))) * phiStd a₂ (-(t * (m 0 1 + x * m 1 1))) * psi (-x) with hf
  have hshift : (fun x : ℝ =>
      phiStd a₁ (-(t * (m 0 0 + x₀ * m 1 0 + x * m 1 0))) * phiStd a₂ (-(t * (m 0 1 + x₀ * m 1 1 + x * m 1 1)))
        * psi (-x)) = fun x : ℝ => f (x + x₀) * psi x₀ := by
    funext x
    simp only [hf]
    have hpsi : psi (-x) = psi (-(x + x₀)) * psi x₀ := by
      rw [← psi_add]; congr 1; ring
    rw [hpsi]
    ring_nf
  rw [hshift]
  have h1 : (∫ x : ℝ, f (x + x₀) * psi x₀) = (∫ x : ℝ, f (x + x₀)) * psi x₀ := integral_mul_const _ _
  rw [h1, integral_add_right_eq_self]
  ring

private theorem Wmem_unip (x₀ : ℝ) (m : Matrix (Fin 2) (Fin 2) ℝ) :
    Wmem u₁ u₂ a₁ a₂ (unip x₀ * m) = psi x₀ * Wmem u₁ u₂ a₁ a₂ m := by
  unfold Wmem
  rw [det_unip_mul]
  simp only [innerW_unip, mul_assoc]
  have h2 : (∫ t : ℝ, psi x₀ * (innerW a₁ a₂ m t * quasiChar (u₁ - u₂) (a₁ + a₂) t))
      = psi x₀ * ∫ t : ℝ, innerW a₁ a₂ m t * quasiChar (u₁ - u₂) (a₁ + a₂) t := integral_const_mul _ _
  rw [h2]
  ring

private theorem sign_mul_self_eq_one {z : ℝ} (hz : z ≠ 0) :
    (((SignType.sign z : ℝ)) : ℂ) * (((SignType.sign z : ℝ)) : ℂ) = 1 := by
  rcases hz.lt_or_gt with h | h
  · simp [sign_neg h]
  · simp [sign_pos h]

private theorem quasiChar_sq_eq {z : ℝ} (hz : z ≠ 0) :
    quasiChar u₁ a₁ z * quasiChar u₁ a₁ z
      = quasiChar (u₁ - u₂) (a₁ + a₂) z * quasiChar (u₁ + u₂) (a₁ + a₂) z := by
  have habs : ((|z| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (abs_pos.mpr hz).ne'
  have hpow : ((|z| : ℝ) : ℂ) ^ u₁ * ((|z| : ℝ) : ℂ) ^ u₁
      = ((|z| : ℝ) : ℂ) ^ (u₁ - u₂) * ((|z| : ℝ) : ℂ) ^ (u₁ + u₂) := by
    rw [← Complex.cpow_add _ _ habs, ← Complex.cpow_add _ _ habs]; congr 1; ring
  have hs := sign_mul_self_eq_one hz
  unfold quasiChar
  set σ : ℂ := (((SignType.sign z : ℝ)) : ℂ) with hσ
  by_cases h1 : a₁ = 0 <;> by_cases h2 : a₁ + a₂ = 0 <;> simp only [h2, if_true, if_false] <;>
    simp only [h1, if_true, if_false, mul_one]
  · linear_combination hpow
  · linear_combination hpow - (((|z| : ℝ) : ℂ) ^ (u₁ - u₂) * ((|z| : ℝ) : ℂ) ^ (u₁ + u₂)) * hs
  · linear_combination (σ * σ) * hpow + (((|z| : ℝ) : ℂ) ^ (u₁ - u₂) * ((|z| : ℝ) : ℂ) ^ (u₁ + u₂)) * hs
  · linear_combination (σ * σ) * hpow

private theorem det_smul_two (z : ℝ) (m : Matrix (Fin 2) (Fin 2) ℝ) : (z • m).det = z ^ 2 * m.det := by
  rw [Matrix.det_smul]; simp

private theorem innerW_smul (z : ℝ) (m : Matrix (Fin 2) (Fin 2) ℝ) (t : ℝ) :
    innerW a₁ a₂ (z • m) t = innerW a₁ a₂ m (z * t) := by
  unfold innerW
  congr 1; funext x
  simp only [Matrix.smul_apply, smul_eq_mul]
  congr 3 <;> ring

private theorem Wmem_smul {z : ℝ} (hz : z ≠ 0) (m : Matrix (Fin 2) (Fin 2) ℝ) :
    Wmem u₁ u₂ a₁ a₂ (z • m) = quasiChar (u₁ + u₂) (a₁ + a₂) z * ((|z| : ℝ) : ℂ) * Wmem u₁ u₂ a₁ a₂ m := by
  unfold Wmem
  rw [det_smul_two]
  have hq : ∀ t : ℝ, quasiChar (u₁ - u₂) (a₁ + a₂) (z * t)
      = quasiChar (u₁ - u₂) (a₁ + a₂) z * quasiChar (u₁ - u₂) (a₁ + a₂) t := fun t => quasiChar_mul' _ _ _ _
  have hqz : quasiChar (u₁ - u₂) (a₁ + a₂) z ≠ 0 := quasiChar_ne_zero _ _ hz
  have hint : (∫ t : ℝ, innerW a₁ a₂ (z • m) t * quasiChar (u₁ - u₂) (a₁ + a₂) t)
      = (quasiChar (u₁ - u₂) (a₁ + a₂) z)⁻¹ * ((|z⁻¹| : ℝ) : ℂ) *
          ∫ t : ℝ, innerW a₁ a₂ m t * quasiChar (u₁ - u₂) (a₁ + a₂) t := by
    have h1 : (fun t : ℝ => innerW a₁ a₂ (z • m) t * quasiChar (u₁ - u₂) (a₁ + a₂) t)
        = fun t : ℝ => (quasiChar (u₁ - u₂) (a₁ + a₂) z)⁻¹ *
            (innerW a₁ a₂ m (z * t) * quasiChar (u₁ - u₂) (a₁ + a₂) (z * t)) := by
      funext t
      rw [innerW_smul, hq t]
      field_simp
    rw [h1]
    have h2 : (∫ t : ℝ, (quasiChar (u₁ - u₂) (a₁ + a₂) z)⁻¹ *
          (innerW a₁ a₂ m (z * t) * quasiChar (u₁ - u₂) (a₁ + a₂) (z * t)))
        = (quasiChar (u₁ - u₂) (a₁ + a₂) z)⁻¹ *
          ∫ t : ℝ, innerW a₁ a₂ m (z * t) * quasiChar (u₁ - u₂) (a₁ + a₂) (z * t) := integral_const_mul _ _
    rw [h2]
    have h3 : (∫ t : ℝ, innerW a₁ a₂ m (z * t) * quasiChar (u₁ - u₂) (a₁ + a₂) (z * t))
        = |z⁻¹| • ∫ t : ℝ, innerW a₁ a₂ m t * quasiChar (u₁ - u₂) (a₁ + a₂) t :=
      Measure.integral_comp_mul_left (fun t : ℝ => innerW a₁ a₂ m t * quasiChar (u₁ - u₂) (a₁ + a₂) t) z
    rw [h3, Complex.real_smul]
    ring
  rw [hint]
  have hdet : (((|z ^ 2 * m.det| : ℝ)) : ℂ) = ((|z| : ℝ) : ℂ) * ((|z| : ℝ) : ℂ) * ((|m.det| : ℝ) : ℂ) := by
    rw [abs_mul, abs_pow]; push_cast; ring
  have hq1 : quasiChar u₁ a₁ (z ^ 2 * m.det) = quasiChar u₁ a₁ z * quasiChar u₁ a₁ z * quasiChar u₁ a₁ m.det := by
    rw [quasiChar_mul', pow_two, quasiChar_mul']
  have habs : ((|z| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (abs_pos.mpr hz).ne'
  have hinv : ((|z⁻¹| : ℝ) : ℂ) = (((|z| : ℝ) : ℂ))⁻¹ := by rw [abs_inv]; push_cast; rfl
  have hsq := quasiChar_sq_eq u₁ u₂ a₁ a₂ hz
  rw [hdet, hq1, hinv, hsq]
  field_simp

private theorem Wmem_central (z : ℝ) (m : Matrix (Fin 2) (Fin 2) ℝ) (hz : z ≠ 0) :
    Wmem u₁ u₂ a₁ a₂ (z • m)
      = centralChar (RealArchParam.principal u₁ a₁ u₂ a₂) z * ((|z| : ℝ) : ℂ) * Wmem u₁ u₂ a₁ a₂ m := by
  rw [centralChar, centralExponent_principal, centralSign_principal]
  exact Wmem_smul u₁ u₂ a₁ a₂ hz m

end W2

end TateReal

end

set_option autoImplicit false

open Complex MeasureTheory FourierTransform

noncomputable section

namespace TateReal
namespace W2

open W3 LanglandsTunnell.Converse.ArchR

private theorem phiStd_eq_gaussStd (a : ZMod 2) (v : ℝ) : phiStd a v = gaussStd a v := rfl

private theorem gaussStd_neg (a : ZMod 2) (v : ℝ) : gaussStd a (-v) = sgnW a * gaussStd a v := by
  unfold gaussStd sgnW
  split_ifs with ha
  · push_cast
    ring
  · push_cast
    ring

private theorem sgnW_ne_zero (b : ZMod 2) : sgnW b ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)

private theorem psiZero_one (a₁ a₂ : ZMod 2) (x Y : ℝ) :
    psiZero a₁ a₂ 1 x Y = (sgnW a₁ * sgnW a₂) * (gaussStd a₂ x * gaussStd a₁ Y) := by
  have h00 : (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = 1 := Matrix.one_apply_eq 0
  have h01 : (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = 0 := Matrix.one_apply_ne (by decide)
  have h10 : (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 0 := Matrix.one_apply_ne (by decide)
  have h11 : (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = 1 := Matrix.one_apply_eq 1
  unfold psiZero
  simp only [h00, h01, h10, h11, mul_one, mul_zero, add_zero, zero_add, phiStd_eq_gaussStd, gaussStd_neg]
  ring

private theorem F₁_psiZero_one (a₁ a₂ : ZMod 2) (ξ Y : ℝ) :
    F₁ (psiZero a₁ a₂ 1) ξ Y = (sgnW a₁ * sgnW a₂ * gaussStd a₁ Y) * (epsW a₂ * gaussStd a₂ ξ) := by
  unfold F₁
  have hfun : (fun x : ℝ => psiZero a₁ a₂ 1 x Y)
      = fun x : ℝ => (sgnW a₁ * sgnW a₂ * gaussStd a₁ Y) * gaussStd a₂ x := by
    funext x
    rw [psiZero_one]
    ring
  rw [hfun]
  have e1 := congrFun (fourier_const_mul (sgnW a₁ * sgnW a₂ * gaussStd a₁ Y) (gaussStd a₂)) ξ
  have e2 := congrFun (fourier_gaussStd a₂) ξ
  beta_reduce at e1 e2
  rw [e1, e2]
  unfold epsW
  ring

private theorem Psi_one (a₁ a₂ : ZMod 2) (Y τ : ℝ) :
    Psi a₁ a₂ 1 Y τ = (sgnW a₁ * sgnW a₂ * epsW a₂) * (gaussStd a₁ Y * gaussStd a₂ τ) := by
  show F₁ (psiZero a₁ a₂ 1) τ Y = _
  rw [F₁_psiZero_one]
  ring

private theorem Z_Psi_one (a₁ a₂ : ZMod 2) {w₁ w₂ : ℂ} (h₁ : 0 < w₁.re) (h₂ : 0 < w₂.re) :
    Z (Psi a₁ a₂ 1) a₁ a₂ w₁ w₂
      = (sgnW a₁ * sgnW a₂ * epsW a₂) * (Gammaℝ (w₁ + sh a₁) * Gammaℝ (w₂ + sh a₂)) := by
  unfold Z zint
  have hpt : ∀ p : ℝ × ℝ, Psi a₁ a₂ 1 p.1 p.2 * ker a₁ w₁ p.1 * ker a₂ w₂ p.2
      = (sgnW a₁ * sgnW a₂ * epsW a₂)
          * ((gaussStd a₁ p.1 * ker a₁ w₁ p.1) * (gaussStd a₂ p.2 * ker a₂ w₂ p.2)) := by
    intro p
    rw [Psi_one]
    ring
  simp_rw [hpt]
  rw [integral_const_mul]
  have hprod : (∫ p : ℝ × ℝ, (gaussStd a₁ p.1 * ker a₁ w₁ p.1) * (gaussStd a₂ p.2 * ker a₂ w₂ p.2))
      = (∫ x : ℝ, gaussStd a₁ x * ker a₁ w₁ x) * ∫ y : ℝ, gaussStd a₂ y * ker a₂ w₂ y := by
    rw [Measure.volume_eq_prod]
    exact integral_prod_mul (fun x : ℝ => gaussStd a₁ x * ker a₁ w₁ x) (fun y : ℝ => gaussStd a₂ y * ker a₂ w₂ y)
  rw [hprod, ← tateZeta_eq_integral_ker (gaussStd a₁) a₁ w₁, ← tateZeta_eq_integral_ker (gaussStd a₂) a₂ w₂,
    tateZeta_gaussStd a₁ h₁, tateZeta_gaussStd a₂ h₂]

private theorem Z_Psi_one_ne_zero (a₁ a₂ : ZMod 2) {w₁ w₂ : ℂ} (h₁ : 0 < w₁.re) (h₂ : 0 < w₂.re) :
    Z (Psi a₁ a₂ 1) a₁ a₂ w₁ w₂ ≠ 0 := by
  rw [Z_Psi_one a₁ a₂ h₁ h₂]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (sgnW_ne_zero a₁) (sgnW_ne_zero a₂)) (epsW_ne_zero a₂))
    (mul_ne_zero (Gammaℝ_add_sh_ne_zero h₁ a₁) (Gammaℝ_add_sh_ne_zero h₂ a₂))

private theorem quasiChar_one (u : ℂ) (a : ZMod 2) : quasiChar u a 1 = 1 := by
  rw [quasiChar_eq]
  unfold sgnPow
  simp

private theorem exists_Wmem_diagOne_ne_zero (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2) :
    ∃ y : ℝ, Wmem u₁ u₂ a₁ a₂ (diagOne y) ≠ 0 := by
  by_contra h
  simp only [not_exists, not_ne_iff] at h
  set σ : ℝ := max (-u₁.re) (-u₂.re) + 1 with hσ
  have h₁ : 0 < ((σ : ℂ) + 0 + u₁).re := by
    simp only [add_re, ofReal_re, add_zero]
    have := le_max_left (-u₁.re) (-u₂.re)
    linarith
  have h₂ : 0 < ((σ : ℂ) + 0 + u₂).re := by
    simp only [add_re, ofReal_re, add_zero]
    have := le_max_right (-u₁.re) (-u₂.re)
    linarith
  have hdet : (1 : Matrix (Fin 2) (Fin 2) ℝ).det ≠ 0 := by
    rw [Matrix.det_one]
    exact one_ne_zero
  have hb := bridge u₁ u₂ 0 a₁ a₂ 0 (σ : ℂ) 1 hdet h₁ h₂
  have hL : (∫ y : ℝ, zetaIntegrand (Wmem u₁ u₂ a₁ a₂) 1 0 0 (σ : ℂ) y) = 0 := by
    have hzero : (fun y : ℝ => zetaIntegrand (Wmem u₁ u₂ a₁ a₂) 1 0 0 (σ : ℂ) y) = fun _ => 0 := by
      funext y
      unfold zetaIntegrand
      rw [Matrix.mul_one, h y, zero_mul, zero_mul, zero_mul]
    rw [hzero, integral_zero]
  have hR : (((|(1 : Matrix (Fin 2) (Fin 2) ℝ).det| : ℝ) : ℂ) * quasiChar u₁ a₁ (1 : Matrix (Fin 2) (Fin 2) ℝ).det)
      * Z (Psi a₁ a₂ 1) (0 + a₁) (0 + a₂) ((σ : ℂ) + 0 + u₁) ((σ : ℂ) + 0 + u₂) ≠ 0 := by
    rw [Matrix.det_one, zero_add, zero_add, abs_one, quasiChar_one, ofReal_one, one_mul, one_mul]
    exact Z_Psi_one_ne_zero a₁ a₂ h₁ h₂
  exact hR (hb.symm.trans hL)

private theorem Wmem_eq_zero_of_det_eq_zero (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2) {g : Matrix (Fin 2) (Fin 2) ℝ}
    (hg : g.det = 0) : Wmem u₁ u₂ a₁ a₂ g = 0 := by
  unfold Wmem
  rw [hg, abs_zero, ofReal_zero, zero_mul, zero_mul]

private theorem exists_Wmem_GL_ne_zero (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2) :
    ∃ g : GL (Fin 2) ℝ, Wmem u₁ u₂ a₁ a₂ (g : Matrix (Fin 2) (Fin 2) ℝ) ≠ 0 := by
  obtain ⟨y, hy⟩ := exists_Wmem_diagOne_ne_zero u₁ u₂ a₁ a₂
  have hdet : (diagOne y).det ≠ 0 := fun h => hy (Wmem_eq_zero_of_det_eq_zero u₁ u₂ a₁ a₂ h)
  exact ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (diagOne y) hdet, hy⟩

end TateReal.W2

end

open Complex MeasureTheory
open scoped FourierTransform

noncomputable section

namespace ArchEngine

local notation "X₄" => (Fin 2 → Fin 2 → ℝ)

private def coordCLM (i j : Fin 2) : X₄ →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) j).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => Fin 2 → ℝ) i)

@[scoped simp] private theorem coordCLM_apply (i j : Fin 2) (e : X₄) : coordCLM i j e = e i j := by
  simp [coordCLM]

private theorem hasFDerivAt_coord (i j : Fin 2) (m : X₄) : HasFDerivAt (fun m : X₄ => m i j) (coordCLM i j) m :=
  (coordCLM i j).hasFDerivAt.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun e => (coordCLM_apply i j e).symm)

private theorem hasFDerivAt_coord_ofReal (i j : Fin 2) (m : X₄) :
    HasFDerivAt (fun m : X₄ => ((m i j : ℝ) : ℂ)) (Complex.ofRealCLM.comp (coordCLM i j)) m :=
  Complex.ofRealCLM.hasFDerivAt.comp m (hasFDerivAt_coord i j m)

private def sumForm (c : Fin 2 → Fin 2 → ℂ) : X₄ →L[ℝ] ℂ :=
  ∑ i : Fin 2, ∑ j : Fin 2, (coordCLM i j).smulRight (c i j)

private theorem sumForm_apply (c : Fin 2 → Fin 2 → ℂ) (v : X₄) :
    sumForm c v = ∑ i : Fin 2, ∑ j : Fin 2, ((v i j : ℝ) : ℂ) * c i j := by
  simp [sumForm, Complex.real_smul]

private inductive IsPoly : (X₄ → ℝ → ℝ → ℂ) → Prop
  | const (c : ℂ) : IsPoly fun _ _ _ => c
  | rowOne (j : Fin 2) : IsPoly fun m _ _ => ((m 1 j : ℝ) : ℂ)
  | rowZeroY (j : Fin 2) : IsPoly fun m _ Y => ((Y : ℝ) : ℂ) * ((m 0 j : ℝ) : ℂ)
  | varX : IsPoly fun _ x _ => ((x : ℝ) : ℂ)
  | varY : IsPoly fun _ _ Y => ((Y : ℝ) : ℂ)
  | add {P Q : X₄ → ℝ → ℝ → ℂ} (hP : IsPoly P) (hQ : IsPoly Q) : IsPoly fun m x Y => P m x Y + Q m x Y
  | mul {P Q : X₄ → ℝ → ℝ → ℂ} (hP : IsPoly P) (hQ : IsPoly Q) : IsPoly fun m x Y => P m x Y * Q m x Y

namespace IsPoly

private theorem congr {P Q : X₄ → ℝ → ℝ → ℂ} (h : IsPoly P) (e : P = Q) : IsPoly Q := e ▸ h

private theorem smul {P : X₄ → ℝ → ℝ → ℂ} (h : IsPoly P) (c : ℂ) : IsPoly fun m x Y => c * P m x Y :=
  (const c).mul h

private theorem neg {P : X₄ → ℝ → ℝ → ℂ} (h : IsPoly P) : IsPoly fun m x Y => -P m x Y :=
  (h.smul (-1)).congr (by funext m x Y; ring)

private theorem sub {P Q : X₄ → ℝ → ℝ → ℂ} (hP : IsPoly P) (hQ : IsPoly Q) :
    IsPoly fun m x Y => P m x Y - Q m x Y :=
  (hP.add hQ.neg).congr (by funext m x Y; ring)

private theorem parityForm (j₀ j₁ : Fin 2) :
    IsPoly fun m x Y => -(((Y : ℝ) : ℂ) * ((m 0 j₀ : ℝ) : ℂ) + ((x : ℝ) : ℂ) * ((m 1 j₁ : ℝ) : ℂ)) :=
  ((rowZeroY j₀).add (varX.mul (rowOne j₁))).neg

private theorem contDiff_x {P : X₄ → ℝ → ℝ → ℂ} (h : IsPoly P) (m : X₄) (Y : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) fun x : ℝ => P m x Y := by
  induction h with
  | const c => exact contDiff_const
  | rowOne j => exact contDiff_const
  | rowZeroY j => exact contDiff_const
  | varX =>
    show ContDiff ℝ (⊤ : ℕ∞) fun x : ℝ => ((x : ℝ) : ℂ)
    have e : (fun x : ℝ => ((x : ℝ) : ℂ)) = ⇑Complex.ofRealCLM := by funext x; simp
    rw [e]
    exact Complex.ofRealCLM.contDiff
  | varY => exact contDiff_const
  | add _ _ ihP ihQ => exact ihP.add ihQ
  | mul _ _ ihP ihQ => exact ihP.mul ihQ

private theorem hasDerivAt_x {P : X₄ → ℝ → ℝ → ℂ} (h : IsPoly P) :
    ∃ P' : X₄ → ℝ → ℝ → ℂ, IsPoly P' ∧ ∀ (m : X₄) (x Y : ℝ), HasDerivAt (fun x => P m x Y) (P' m x Y) x := by
  induction h with
  | const c => exact ⟨fun _ _ _ => 0, const 0, fun m x Y => hasDerivAt_const x c⟩
  | rowOne j => exact ⟨fun _ _ _ => 0, const 0, fun m x Y => hasDerivAt_const x _⟩
  | rowZeroY j => exact ⟨fun _ _ _ => 0, const 0, fun m x Y => hasDerivAt_const x _⟩
  | varX => exact ⟨fun _ _ _ => 1, const 1, fun m x Y => by simpa using (hasDerivAt_id x).ofReal_comp⟩
  | varY => exact ⟨fun _ _ _ => 0, const 0, fun m x Y => hasDerivAt_const x _⟩
  | @add P Q _ _ ihP ihQ =>
    obtain ⟨P', hP', hdP⟩ := ihP
    obtain ⟨Q', hQ', hdQ⟩ := ihQ
    exact ⟨fun m x Y => P' m x Y + Q' m x Y, hP'.add hQ', fun m x Y => (hdP m x Y).add (hdQ m x Y)⟩
  | @mul P Q hP hQ ihP ihQ =>
    obtain ⟨P', hP', hdP⟩ := ihP
    obtain ⟨Q', hQ', hdQ⟩ := ihQ
    exact ⟨fun m x Y => P' m x Y * Q m x Y + P m x Y * Q' m x Y, (hP'.mul hQ).add (hP.mul hQ'),
      fun m x Y => (hdP m x Y).mul (hdQ m x Y)⟩

private theorem hasFDerivAt_m {P : X₄ → ℝ → ℝ → ℂ} (h : IsPoly P) :
    ∃ D : Fin 2 → Fin 2 → X₄ → ℝ → ℝ → ℂ, (∀ i j, IsPoly (D i j)) ∧
      ∀ (m : X₄) (x Y : ℝ), HasFDerivAt (fun m => P m x Y) (sumForm fun i j => D i j m x Y) m := by
  induction h with
  | const c =>
    refine ⟨fun _ _ _ _ _ => 0, fun _ _ => const 0, fun m x Y => ?_⟩
    refine (hasFDerivAt_const c m).congr_fderiv ?_
    refine ContinuousLinearMap.ext fun v => ?_
    simp [sumForm_apply]
  | rowOne j₀ =>
    refine ⟨fun i j _ _ _ => if i = 1 ∧ j = j₀ then (1 : ℂ) else 0, fun i j => ?_, fun m x Y => ?_⟩
    · by_cases hc : i = 1 ∧ j = j₀
      · simp only [hc, and_self, if_true]
        exact const 1
      · simp only [hc, if_false]
        exact const 0
    · refine (hasFDerivAt_coord_ofReal 1 j₀ m).congr_fderiv ?_
      refine ContinuousLinearMap.ext fun v => ?_
      fin_cases j₀ <;> simp [sumForm_apply, Fin.sum_univ_two]
  | rowZeroY j₀ =>
    refine ⟨fun i j _ _ Y => if i = 0 ∧ j = j₀ then ((Y : ℝ) : ℂ) else 0, fun i j => ?_, fun m x Y => ?_⟩
    · by_cases hc : i = 0 ∧ j = j₀
      · simp only [hc, and_self, if_true]
        exact varY
      · simp only [hc, if_false]
        exact const 0
    · refine ((hasFDerivAt_coord_ofReal 0 j₀ m).const_mul ((Y : ℝ) : ℂ)).congr_fderiv ?_
      refine ContinuousLinearMap.ext fun v => ?_
      fin_cases j₀ <;> simp [sumForm_apply, Fin.sum_univ_two] <;> ring
  | varX =>
    refine ⟨fun _ _ _ _ _ => 0, fun _ _ => const 0, fun m x Y => ?_⟩
    refine (hasFDerivAt_const ((x : ℝ) : ℂ) m).congr_fderiv ?_
    refine ContinuousLinearMap.ext fun v => ?_
    simp [sumForm_apply]
  | varY =>
    refine ⟨fun _ _ _ _ _ => 0, fun _ _ => const 0, fun m x Y => ?_⟩
    refine (hasFDerivAt_const ((Y : ℝ) : ℂ) m).congr_fderiv ?_
    refine ContinuousLinearMap.ext fun v => ?_
    simp [sumForm_apply]
  | @add P Q _ _ ihP ihQ =>
    obtain ⟨D₁, hD₁, hd₁⟩ := ihP
    obtain ⟨D₂, hD₂, hd₂⟩ := ihQ
    refine ⟨fun i j m x Y => D₁ i j m x Y + D₂ i j m x Y, fun i j => (hD₁ i j).add (hD₂ i j), fun m x Y => ?_⟩
    refine ((hd₁ m x Y).add (hd₂ m x Y)).congr_fderiv ?_
    refine ContinuousLinearMap.ext fun v => ?_
    simp only [ContinuousLinearMap.add_apply, sumForm_apply, Fin.sum_univ_two]
    ring
  | @mul P Q hP hQ ihP ihQ =>
    obtain ⟨D₁, hD₁, hd₁⟩ := ihP
    obtain ⟨D₂, hD₂, hd₂⟩ := ihQ
    refine ⟨fun i j m x Y => P m x Y * D₂ i j m x Y + Q m x Y * D₁ i j m x Y,
      fun i j => (hP.mul (hD₂ i j)).add (hQ.mul (hD₁ i j)), fun m x Y => ?_⟩
    refine ((hd₁ m x Y).mul (hd₂ m x Y)).congr_fderiv ?_
    refine ContinuousLinearMap.ext fun v => ?_
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, sumForm_apply, Fin.sum_univ_two,
      smul_eq_mul]
    ring

private theorem differentiable_m
    {P : X₄ → ℝ → ℝ → ℂ} (h : IsPoly P) (x Y : ℝ) : Differentiable ℝ fun m : X₄ => P m x Y := by
  obtain ⟨D, -, hd⟩ := h.hasFDerivAt_m
  exact fun m => (hd m x Y).differentiableAt

end IsPoly

private def qForm (m : X₄) (x Y : ℝ) : ℝ := (Y * m 0 0 + x * m 1 0) ^ 2 + (Y * m 0 1 + x * m 1 1) ^ 2

private def expo (m : X₄) (x Y : ℝ) : ℂ := -(Real.pi : ℂ) * ((qForm m x Y : ℝ) : ℂ)

private theorem isPoly_expo : IsPoly expo := by
  have hL : ∀ j : Fin 2,
      IsPoly fun m x Y => ((Y : ℝ) : ℂ) * ((m 0 j : ℝ) : ℂ) + ((x : ℝ) : ℂ) * ((m 1 j : ℝ) : ℂ) :=
    fun j => (IsPoly.rowZeroY j).add (IsPoly.varX.mul (IsPoly.rowOne j))
  refine IsPoly.congr ((((hL 0).mul (hL 0)).add ((hL 1).mul (hL 1))).smul (-(Real.pi : ℂ))) ?_
  funext m x Y
  simp only [expo, qForm]
  push_cast
  ring

private def gaussW (m : X₄) (x Y : ℝ) : ℂ := Complex.exp (expo m x Y)

private theorem norm_gaussW (m : X₄) (x Y : ℝ) : ‖gaussW m x Y‖ = Real.exp (-Real.pi * qForm m x Y) := by
  simp [gaussW, expo, Complex.norm_exp]

private theorem gaussW_ne_zero (m : X₄) (x Y : ℝ) : gaussW m x Y ≠ 0 := Complex.exp_ne_zero _

private def phiFam (P : X₄ → ℝ → ℝ → ℂ) (m : X₄) (x Y : ℝ) : ℂ := P m x Y * gaussW m x Y

namespace IsPoly

private theorem contDiff_x_phiFam {P : X₄ → ℝ → ℝ → ℂ} (h : IsPoly P) (m : X₄) (Y : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) fun x : ℝ => phiFam P m x Y := by
  have hE := isPoly_expo.contDiff_x m Y
  have hg : ContDiff ℝ (⊤ : ℕ∞) fun x : ℝ => gaussW m x Y := Complex.contDiff_exp.comp hE
  exact (h.contDiff_x m Y).mul hg

private theorem hasDerivAt_x_phiFam {P : X₄ → ℝ → ℝ → ℂ} (h : IsPoly P) :
    ∃ P₁ : X₄ → ℝ → ℝ → ℂ, IsPoly P₁ ∧
      ∀ (m : X₄) (x Y : ℝ), HasDerivAt (fun x => phiFam P m x Y) (phiFam P₁ m x Y) x := by
  obtain ⟨P', hP', hdP⟩ := h.hasDerivAt_x
  obtain ⟨E', hE', hdE⟩ := isPoly_expo.hasDerivAt_x
  refine ⟨fun m x Y => P' m x Y + P m x Y * E' m x Y, hP'.add (h.mul hE'), fun m x Y => ?_⟩
  have hg : HasDerivAt (fun x => gaussW m x Y) (gaussW m x Y * E' m x Y) x := (hdE m x Y).cexp
  refine ((hdP m x Y).mul hg).congr_deriv ?_
  simp only [phiFam]
  ring

private theorem hasFDerivAt_m_phiFam {P : X₄ → ℝ → ℝ → ℂ} (h : IsPoly P) :
    ∃ D : Fin 2 → Fin 2 → X₄ → ℝ → ℝ → ℂ, (∀ i j, IsPoly (D i j)) ∧
      ∀ (m : X₄) (x Y : ℝ),
        HasFDerivAt (fun m => phiFam P m x Y) (sumForm fun i j => phiFam (D i j) m x Y) m := by
  obtain ⟨DP, hDP, hdP⟩ := h.hasFDerivAt_m
  obtain ⟨DE, hDE, hdE⟩ := isPoly_expo.hasFDerivAt_m
  refine ⟨fun i j m x Y => DP i j m x Y + P m x Y * DE i j m x Y,
    fun i j => (hDP i j).add (h.mul (hDE i j)), fun m x Y => ?_⟩
  have hg : HasFDerivAt (fun m => gaussW m x Y) (gaussW m x Y • sumForm fun i j => DE i j m x Y) m :=
    (hdE m x Y).cexp
  show HasFDerivAt (fun m => P m x Y * gaussW m x Y) _ m
  refine ((hdP m x Y).mul hg).congr_fderiv ?_
  refine ContinuousLinearMap.ext fun v => ?_
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, sumForm_apply, Fin.sum_univ_two,
    smul_eq_mul, phiFam]
  ring

private theorem iteratedDeriv_x_phiFam {P : X₄ → ℝ → ℝ → ℂ} (h : IsPoly P) (n : ℕ) :
    ∃ Pₙ : X₄ → ℝ → ℝ → ℂ, IsPoly Pₙ ∧
      ∀ (m : X₄) (Y : ℝ), iteratedDeriv n (fun x => phiFam P m x Y) = fun x => phiFam Pₙ m x Y := by
  induction n generalizing P with
  | zero => exact ⟨P, h, fun m Y => by rw [iteratedDeriv_zero]⟩
  | succ n ih =>
    obtain ⟨P₁, hP₁, hd₁⟩ := h.hasDerivAt_x_phiFam
    obtain ⟨Pₙ, hPₙ, hPn⟩ := ih (P := P₁) hP₁
    refine ⟨Pₙ, hPₙ, fun m Y => ?_⟩
    rw [iteratedDeriv_succ']
    have e : deriv (fun x => phiFam P m x Y) = fun x => phiFam P₁ m x Y :=
      funext fun x => (hd₁ m x Y).deriv
    rw [e, hPn m Y]

end IsPoly

private inductive IsEntryPoly : (X₄ → ℂ) → Prop
  | const (c : ℂ) : IsEntryPoly fun _ => c
  | entry (i j : Fin 2) : IsEntryPoly fun m => ((m i j : ℝ) : ℂ)
  | add {R S : X₄ → ℂ} (hR : IsEntryPoly R) (hS : IsEntryPoly S) : IsEntryPoly fun m => R m + S m
  | mul {R S : X₄ → ℂ} (hR : IsEntryPoly R) (hS : IsEntryPoly S) : IsEntryPoly fun m => R m * S m

namespace IsEntryPoly

private theorem congr {R S : X₄ → ℂ} (h : IsEntryPoly R) (e : R = S) : IsEntryPoly S := e ▸ h

private theorem smul {R : X₄ → ℂ} (h : IsEntryPoly R) (c : ℂ) : IsEntryPoly fun m => c * R m := (const c).mul h

private theorem neg {R : X₄ → ℂ} (h : IsEntryPoly R) : IsEntryPoly fun m => -R m :=
  (h.smul (-1)).congr (by funext m; ring)

private theorem sub {R S : X₄ → ℂ} (hR : IsEntryPoly R) (hS : IsEntryPoly S) : IsEntryPoly fun m => R m - S m :=
  (hR.add hS.neg).congr (by funext m; ring)

private theorem detCoords :
    IsEntryPoly fun m : X₄ =>
      ((m 0 0 : ℝ) : ℂ) * ((m 1 1 : ℝ) : ℂ) - ((m 0 1 : ℝ) : ℂ) * ((m 1 0 : ℝ) : ℂ) :=
  ((entry 0 0).mul (entry 1 1)).sub ((entry 0 1).mul (entry 1 0))

private theorem detCoords_eq (m : X₄) :
    ((m 0 0 : ℝ) : ℂ) * ((m 1 1 : ℝ) : ℂ) - ((m 0 1 : ℝ) : ℂ) * ((m 1 0 : ℝ) : ℂ) = (((Matrix.of m).det : ℝ) : ℂ) := by
  rw [Matrix.det_fin_two]
  simp [Matrix.of_apply]

private theorem hasFDerivAt {R : X₄ → ℂ} (h : IsEntryPoly R) :
    ∃ D : Fin 2 → Fin 2 → X₄ → ℂ, (∀ i j, IsEntryPoly (D i j)) ∧
      ∀ m : X₄, HasFDerivAt R (sumForm fun i j => D i j m) m := by
  induction h with
  | const c =>
    refine ⟨fun _ _ _ => 0, fun _ _ => const 0, fun m => ?_⟩
    refine (hasFDerivAt_const c m).congr_fderiv ?_
    refine ContinuousLinearMap.ext fun v => ?_
    simp [sumForm_apply]
  | entry i₀ j₀ =>
    refine ⟨fun i j _ => if i = i₀ ∧ j = j₀ then (1 : ℂ) else 0, fun i j => ?_, fun m => ?_⟩
    · by_cases hc : i = i₀ ∧ j = j₀
      · simp only [hc, and_self, if_true]
        exact const 1
      · simp only [hc, if_false]
        exact const 0
    · refine (hasFDerivAt_coord_ofReal i₀ j₀ m).congr_fderiv ?_
      refine ContinuousLinearMap.ext fun v => ?_
      fin_cases i₀ <;> fin_cases j₀ <;> simp [sumForm_apply, Fin.sum_univ_two]
  | @add R S _ _ ihR ihS =>
    obtain ⟨D₁, hD₁, hd₁⟩ := ihR
    obtain ⟨D₂, hD₂, hd₂⟩ := ihS
    refine ⟨fun i j m => D₁ i j m + D₂ i j m, fun i j => (hD₁ i j).add (hD₂ i j), fun m => ?_⟩
    refine ((hd₁ m).add (hd₂ m)).congr_fderiv ?_
    refine ContinuousLinearMap.ext fun v => ?_
    simp only [ContinuousLinearMap.add_apply, sumForm_apply, Fin.sum_univ_two]
    ring
  | @mul R S hR hS ihR ihS =>
    obtain ⟨D₁, hD₁, hd₁⟩ := ihR
    obtain ⟨D₂, hD₂, hd₂⟩ := ihS
    refine ⟨fun i j m => R m * D₂ i j m + S m * D₁ i j m,
      fun i j => (hR.mul (hD₂ i j)).add (hS.mul (hD₁ i j)), fun m => ?_⟩
    refine ((hd₁ m).mul (hd₂ m)).congr_fderiv ?_
    refine ContinuousLinearMap.ext fun v => ?_
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, sumForm_apply, Fin.sum_univ_two,
      smul_eq_mul]
    ring

private theorem differentiable {R : X₄ → ℂ} (h : IsEntryPoly R) : Differentiable ℝ R := by
  obtain ⟨D, -, hd⟩ := h.hasFDerivAt
  exact fun m => (hd m).differentiableAt

end IsEntryPoly

namespace IsPoly

private theorem norm_le_of_gen_le {P : X₄ → ℝ → ℝ → ℂ} (h : IsPoly P) :
    ∃ (C : ℝ) (d : ℕ), 0 ≤ C ∧ ∀ (m : X₄) (x Y B : ℝ), 1 ≤ B → (∀ j, |m 1 j| ≤ B) →
      (∀ j, |Y * m 0 j| ≤ B) → |x| ≤ B → |Y| ≤ B → ‖P m x Y‖ ≤ C * B ^ d := by
  induction h with
  | const c => exact ⟨‖c‖, 0, norm_nonneg c, fun m x Y B _ _ _ _ _ => by simp⟩
  | rowOne j =>
    refine ⟨1, 1, zero_le_one, fun m x Y B _ h1 _ _ _ => ?_⟩
    simpa [Complex.norm_real, Real.norm_eq_abs] using h1 j
  | rowZeroY j =>
    refine ⟨1, 1, zero_le_one, fun m x Y B _ _ h0 _ _ => ?_⟩
    simpa [Complex.norm_real, Real.norm_eq_abs, abs_mul] using h0 j
  | varX =>
    refine ⟨1, 1, zero_le_one, fun m x Y B _ _ _ hx _ => ?_⟩
    simpa [Complex.norm_real, Real.norm_eq_abs] using hx
  | varY =>
    refine ⟨1, 1, zero_le_one, fun m x Y B _ _ _ _ hY => ?_⟩
    simpa [Complex.norm_real, Real.norm_eq_abs] using hY
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

private theorem norm_le_of_entries_le {R : X₄ → ℂ} (h : IsEntryPoly R) :
    ∃ (C : ℝ) (d : ℕ), 0 ≤ C ∧ ∀ (m : X₄) (B : ℝ), 1 ≤ B → (∀ i j, |m i j| ≤ B) → ‖R m‖ ≤ C * B ^ d := by
  induction h with
  | const c => exact ⟨‖c‖, 0, norm_nonneg c, fun m B _ _ => by simp⟩
  | entry i j =>
    refine ⟨1, 1, zero_le_one, fun m B _ hm => ?_⟩
    simpa [Complex.norm_real, Real.norm_eq_abs] using hm i j
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

private def detX (m : X₄) : ℝ := m 0 0 * m 1 1 - m 0 1 * m 1 0

private def frobX (m : X₄) : ℝ := m 0 0 ^ 2 + m 0 1 ^ 2 + m 1 0 ^ 2 + m 1 1 ^ 2

private theorem continuous_detX : Continuous detX := by
  unfold detX
  fun_prop

private theorem continuous_frobX : Continuous frobX := by
  unfold frobX
  fun_prop

private theorem abs_detX_le (m : X₄) : |detX m| ≤ frobX m / 2 := by
  unfold detX frobX
  refine abs_le.mpr ⟨?_, ?_⟩ <;>
    nlinarith [sq_nonneg (m 0 0 - m 1 1), sq_nonneg (m 0 0 + m 1 1), sq_nonneg (m 0 1 - m 1 0),
      sq_nonneg (m 0 1 + m 1 0)]

private theorem frobX_pos_of_detX_ne_zero {m : X₄} (hm : detX m ≠ 0) : 0 < frobX m := by
  have h1 : 0 < |detX m| := abs_pos.mpr hm
  linarith [abs_detX_le m]

private theorem detX_sq_mul_le (m : X₄) (x Y : ℝ) : detX m ^ 2 * (x ^ 2 + Y ^ 2) ≤ qForm m x Y * frobX m := by
  have key : qForm m x Y * frobX m = detX m ^ 2 * (x ^ 2 + Y ^ 2)
      + ((Y * m 0 0 + x * m 1 0) * m 1 0 + (Y * m 0 1 + x * m 1 1) * m 1 1) ^ 2
      + ((Y * m 0 0 + x * m 1 0) * m 0 0 + (Y * m 0 1 + x * m 1 1) * m 0 1) ^ 2 := by
    unfold qForm frobX detX
    ring
  rw [key]
  nlinarith [sq_nonneg ((Y * m 0 0 + x * m 1 0) * m 1 0 + (Y * m 0 1 + x * m 1 1) * m 1 1),
    sq_nonneg ((Y * m 0 0 + x * m 1 0) * m 0 0 + (Y * m 0 1 + x * m 1 1) * m 0 1)]

private theorem eventually_qForm_ge {m₀ : X₄} (hm₀ : detX m₀ ≠ 0) :
    ∃ σ : ℝ, 0 < σ ∧ ∀ᶠ m in nhds m₀, ∀ x Y : ℝ, σ * (x ^ 2 + Y ^ 2) ≤ qForm m x Y := by
  have hd : 0 < detX m₀ ^ 2 := by positivity
  have hf : 0 < frobX m₀ := frobX_pos_of_detX_ne_zero hm₀
  have hf' : frobX m₀ ≠ 0 := hf.ne'
  refine ⟨detX m₀ ^ 2 / (4 * frobX m₀), by positivity, ?_⟩
  have h1 : ∀ᶠ m in nhds m₀, detX m₀ ^ 2 / 2 < detX m ^ 2 :=
    continuousAt_const.eventually_lt (continuous_detX.pow 2).continuousAt
      (by linarith : detX m₀ ^ 2 / 2 < detX m₀ ^ 2)
  have h2 : ∀ᶠ m in nhds m₀, frobX m < 2 * frobX m₀ :=
    continuous_frobX.continuousAt.eventually_lt continuousAt_const (by linarith : frobX m₀ < 2 * frobX m₀)
  filter_upwards [h1, h2] with m hm1 hm2 x Y
  have hdm : detX m ≠ 0 := by
    intro h0
    rw [h0] at hm1
    linarith
  have hfm : 0 < frobX m := frobX_pos_of_detX_ne_zero hdm
  have e : detX m₀ ^ 2 / (4 * frobX m₀) * (2 * frobX m₀) = detX m₀ ^ 2 / 2 := by
    field_simp
    ring
  have hσ : detX m₀ ^ 2 / (4 * frobX m₀) * frobX m ≤ detX m ^ 2 := by
    have hσ0 : 0 ≤ detX m₀ ^ 2 / (4 * frobX m₀) := by positivity
    have := mul_le_mul_of_nonneg_left hm2.le hσ0
    linarith
  have hs : 0 ≤ x ^ 2 + Y ^ 2 := by positivity
  have h3 : detX m₀ ^ 2 / (4 * frobX m₀) * (x ^ 2 + Y ^ 2) * frobX m ≤ qForm m x Y * frobX m :=
    calc detX m₀ ^ 2 / (4 * frobX m₀) * (x ^ 2 + Y ^ 2) * frobX m
        = (detX m₀ ^ 2 / (4 * frobX m₀) * frobX m) * (x ^ 2 + Y ^ 2) := by ring
      _ ≤ detX m ^ 2 * (x ^ 2 + Y ^ 2) := mul_le_mul_of_nonneg_right hσ hs
      _ ≤ qForm m x Y * frobX m := detX_sq_mul_le m x Y
  exact le_of_mul_le_mul_right h3 hfm

private theorem qForm_of_orthogonal_rows {m : X₄} {y : ℝ} (h0 : m 0 0 ^ 2 + m 0 1 ^ 2 = y ^ 2)
    (h1 : m 1 0 ^ 2 + m 1 1 ^ 2 = 1) (h01 : m 0 0 * m 1 0 + m 0 1 * m 1 1 = 0) (x Y : ℝ) :
    qForm m x Y = x ^ 2 + y ^ 2 * Y ^ 2 := by
  unfold qForm
  linear_combination (Y ^ 2) * h0 + (x ^ 2) * h1 + (2 * x * Y) * h01

private theorem one_add_pow_le_exp (d : ℕ) {c : ℝ} (hc : 0 < c) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s : ℝ, 0 ≤ s → (1 + s) ^ d ≤ K * Real.exp (c * s) := by
  refine ⟨(d.factorial : ℝ) * Real.exp c / c ^ d, by positivity, fun s hs => ?_⟩
  have h : (c * (1 + s)) ^ d / (d.factorial : ℝ) ≤ Real.exp (c * (1 + s)) := by
    exact Real.pow_div_factorial_le_exp _ (by positivity) d
  rw [mul_pow, div_le_iff₀ (by positivity), mul_add, mul_one, Real.exp_add] at h
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  nlinarith [h]

private theorem one_add_abs_add_abs_le (x Y : ℝ) : 1 + |x| + |Y| ≤ 2 * (1 + (x ^ 2 + Y ^ 2)) := by
  nlinarith [sq_nonneg (|x| - 1 / 2), sq_nonneg (|Y| - 1 / 2), sq_abs x, sq_abs Y, abs_nonneg x, abs_nonneg Y]

private theorem entry_abs_le_norm (m : X₄) (i j : Fin 2) : |m i j| ≤ ‖m‖ := by
  rw [← Real.norm_eq_abs]
  exact (norm_le_pi_norm (m i) j).trans (norm_le_pi_norm m i)

private theorem exp_mul_exp_half (c s : ℝ) :
    Real.exp (c / 2 * s) * Real.exp (-c * s) = Real.exp (-(c / 2) * s) := by
  rw [← Real.exp_add]
  congr 1
  ring

namespace IsPoly

private theorem phiFam_bound {Q : X₄ → ℝ → ℝ → ℂ} (hQ : IsPoly Q) {R σ : ℝ} (hR : 0 ≤ R) (hσ : 0 < σ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ m : X₄, ‖m‖ ≤ R → (∀ x Y : ℝ, σ * (x ^ 2 + Y ^ 2) ≤ qForm m x Y) →
      ∀ x Y : ℝ, ‖phiFam Q m x Y‖ ≤ K * Real.exp (-(Real.pi * σ / 2) * (x ^ 2 + Y ^ 2)) := by
  obtain ⟨C, d, hC, hsize⟩ := hQ.norm_le_of_gen_le
  obtain ⟨K₀, hK₀, habs⟩ := one_add_pow_le_exp d (c := Real.pi * σ / 2) (by positivity)
  refine ⟨C * (1 + R) ^ d * 2 ^ d * K₀, by positivity, fun m hm hq x Y => ?_⟩
  have hs : 0 ≤ x ^ 2 + Y ^ 2 := by positivity
  have hax := abs_nonneg x
  have haY := abs_nonneg Y
  have hB1 : (1 : ℝ) ≤ 1 + |x| + |Y| := by linarith
  have hR1 : (1 : ℝ) ≤ 1 + R := by linarith
  have hB1' : (0 : ℝ) ≤ 1 + |x| + |Y| := by linarith
  have hB : 1 ≤ (1 + R) * (1 + |x| + |Y|) := one_le_mul_of_one_le_of_one_le hR1 hB1
  have hRB : 1 + R ≤ (1 + R) * (1 + |x| + |Y|) := le_mul_of_one_le_right (by linarith) hB1
  have hBB : 1 + |x| + |Y| ≤ (1 + R) * (1 + |x| + |Y|) := le_mul_of_one_le_left hB1' hR1
  have hent : ∀ i j, |m i j| ≤ R := fun i j => (entry_abs_le_norm m i j).trans hm
  have h1 : ∀ j, |m 1 j| ≤ (1 + R) * (1 + |x| + |Y|) := fun j => by linarith [hent 1 j]
  have h0 : ∀ j, |Y * m 0 j| ≤ (1 + R) * (1 + |x| + |Y|) := fun j => by
    rw [abs_mul]
    calc |Y| * |m 0 j| ≤ |Y| * R := mul_le_mul_of_nonneg_left (hent 0 j) haY
      _ ≤ (1 + |x| + |Y|) * R := mul_le_mul_of_nonneg_right (by linarith) hR
      _ ≤ (1 + |x| + |Y|) * (1 + R) := mul_le_mul_of_nonneg_left (by linarith) hB1'
      _ = (1 + R) * (1 + |x| + |Y|) := mul_comm _ _
  have hx : |x| ≤ (1 + R) * (1 + |x| + |Y|) := by linarith
  have hY : |Y| ≤ (1 + R) * (1 + |x| + |Y|) := by linarith
  have hQb := hsize m x Y _ hB h1 h0 hx hY
  have h2 : (1 + |x| + |Y|) ^ d ≤ 2 ^ d * (1 + (x ^ 2 + Y ^ 2)) ^ d := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hB1' (one_add_abs_add_abs_le x Y) d
  have h3 := habs (x ^ 2 + Y ^ 2) hs
  have hpoly : ((1 + R) * (1 + |x| + |Y|)) ^ d ≤
      (1 + R) ^ d * 2 ^ d * (K₀ * Real.exp (Real.pi * σ / 2 * (x ^ 2 + Y ^ 2))) := by
    rw [mul_pow]
    calc (1 + R) ^ d * (1 + |x| + |Y|) ^ d ≤ (1 + R) ^ d * (2 ^ d * (1 + (x ^ 2 + Y ^ 2)) ^ d) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ ≤ (1 + R) ^ d * (2 ^ d * (K₀ * Real.exp (Real.pi * σ / 2 * (x ^ 2 + Y ^ 2)))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 (by positivity)) (by positivity)
      _ = (1 + R) ^ d * 2 ^ d * (K₀ * Real.exp (Real.pi * σ / 2 * (x ^ 2 + Y ^ 2))) := by ring
  have hgauss : ‖gaussW m x Y‖ ≤ Real.exp (-(Real.pi * σ) * (x ^ 2 + Y ^ 2)) := by
    rw [norm_gaussW, Real.exp_le_exp]
    have := hq x Y
    nlinarith [Real.pi_pos]
  unfold phiFam
  rw [norm_mul]
  calc ‖Q m x Y‖ * ‖gaussW m x Y‖
      ≤ (C * ((1 + R) * (1 + |x| + |Y|)) ^ d) * Real.exp (-(Real.pi * σ) * (x ^ 2 + Y ^ 2)) :=
        mul_le_mul hQb hgauss (norm_nonneg _) (by positivity)
    _ ≤ (C * ((1 + R) ^ d * 2 ^ d * (K₀ * Real.exp (Real.pi * σ / 2 * (x ^ 2 + Y ^ 2)))))
          * Real.exp (-(Real.pi * σ) * (x ^ 2 + Y ^ 2)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpoly hC) (Real.exp_pos _).le
    _ = C * (1 + R) ^ d * 2 ^ d * K₀ * Real.exp (-(Real.pi * σ / 2) * (x ^ 2 + Y ^ 2)) := by
        rw [← exp_mul_exp_half (Real.pi * σ) (x ^ 2 + Y ^ 2)]
        ring

private theorem phiFam_gate_bound {Q : X₄ → ℝ → ℝ → ℂ} (hQ : IsPoly Q) :
    ∃ (K : ℝ) (d : ℕ), 0 ≤ K ∧ ∀ (m : X₄) (y : ℝ), (∀ j, |m 1 j| ≤ 1) → (∀ j, |m 0 j| ≤ |y|) →
      (∀ x t : ℝ, qForm m x t = x ^ 2 + y ^ 2 * t ^ 2) →
      ∀ x t : ℝ, ‖phiFam Q m x t‖ ≤
        K * (1 + |t|) ^ d * Real.exp (-(Real.pi / 2) * (x ^ 2 + (y * t) ^ 2)) := by
  obtain ⟨C, d, hC, hsize⟩ := hQ.norm_le_of_gen_le
  obtain ⟨K₀, hK₀, habs⟩ := one_add_pow_le_exp d (c := Real.pi / 2) (by positivity)
  refine ⟨C * 2 ^ d * K₀, d, by positivity, fun m y hbot htop hform x t => ?_⟩
  have hs : 0 ≤ x ^ 2 + (y * t) ^ 2 := by positivity
  have hax := abs_nonneg x
  have hat := abs_nonneg t
  have hayt := abs_nonneg (y * t)
  have hA1 : (1 : ℝ) ≤ 1 + |x| + |y * t| := by linarith
  have hA0 : (0 : ℝ) ≤ 1 + |x| + |y * t| := by linarith
  have hT1 : (1 : ℝ) ≤ 1 + |t| := by linarith
  have hB : 1 ≤ (1 + |x| + |y * t|) * (1 + |t|) := one_le_mul_of_one_le_of_one_le hA1 hT1
  have hAB : 1 + |x| + |y * t| ≤ (1 + |x| + |y * t|) * (1 + |t|) := le_mul_of_one_le_right hA0 hT1
  have hTB : 1 + |t| ≤ (1 + |x| + |y * t|) * (1 + |t|) := le_mul_of_one_le_left (by linarith) hA1
  have h1 : ∀ j, |m 1 j| ≤ (1 + |x| + |y * t|) * (1 + |t|) := fun j => by linarith [hbot j]
  have h0 : ∀ j, |t * m 0 j| ≤ (1 + |x| + |y * t|) * (1 + |t|) := fun j => by
    rw [abs_mul]
    have h' : |t| * |m 0 j| ≤ |t| * |y| := mul_le_mul_of_nonneg_left (htop j) hat
    have h'' : |t| * |y| = |y * t| := by rw [abs_mul, mul_comm]
    linarith
  have hx : |x| ≤ (1 + |x| + |y * t|) * (1 + |t|) := by linarith
  have ht : |t| ≤ (1 + |x| + |y * t|) * (1 + |t|) := by linarith
  have hQb := hsize m x t _ hB h1 h0 hx ht
  have h2 : (1 + |x| + |y * t|) ^ d ≤ 2 ^ d * (1 + (x ^ 2 + (y * t) ^ 2)) ^ d := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hA0 (one_add_abs_add_abs_le x (y * t)) d
  have h3 := habs (x ^ 2 + (y * t) ^ 2) hs
  have hpoly : ((1 + |x| + |y * t|) * (1 + |t|)) ^ d ≤
      2 ^ d * (K₀ * Real.exp (Real.pi / 2 * (x ^ 2 + (y * t) ^ 2))) * (1 + |t|) ^ d := by
    rw [mul_pow]
    calc (1 + |x| + |y * t|) ^ d * (1 + |t|) ^ d
        ≤ (2 ^ d * (1 + (x ^ 2 + (y * t) ^ 2)) ^ d) * (1 + |t|) ^ d :=
          mul_le_mul_of_nonneg_right h2 (by positivity)
      _ ≤ (2 ^ d * (K₀ * Real.exp (Real.pi / 2 * (x ^ 2 + (y * t) ^ 2)))) * (1 + |t|) ^ d :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 (by positivity)) (by positivity)
  have hgauss : ‖gaussW m x t‖ = Real.exp (-Real.pi * (x ^ 2 + (y * t) ^ 2)) := by
    rw [norm_gaussW, hform x t]
    congr 1
    ring
  unfold phiFam
  rw [norm_mul, hgauss]
  calc ‖Q m x t‖ * Real.exp (-Real.pi * (x ^ 2 + (y * t) ^ 2))
      ≤ (C * ((1 + |x| + |y * t|) * (1 + |t|)) ^ d) * Real.exp (-Real.pi * (x ^ 2 + (y * t) ^ 2)) :=
        mul_le_mul_of_nonneg_right hQb (Real.exp_pos _).le
    _ ≤ (C * (2 ^ d * (K₀ * Real.exp (Real.pi / 2 * (x ^ 2 + (y * t) ^ 2))) * (1 + |t|) ^ d))
          * Real.exp (-Real.pi * (x ^ 2 + (y * t) ^ 2)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpoly hC) (Real.exp_pos _).le
    _ = C * 2 ^ d * K₀ * (1 + |t|) ^ d * Real.exp (-(Real.pi / 2) * (x ^ 2 + (y * t) ^ 2)) := by
        rw [← exp_mul_exp_half Real.pi (x ^ 2 + (y * t) ^ 2)]
        ring

private theorem integrable_phiFam {Q : X₄ → ℝ → ℝ → ℂ} (hQ : IsPoly Q) {m : X₄} (hm : detX m ≠ 0) (Y : ℝ) :
    MeasureTheory.Integrable fun x : ℝ => phiFam Q m x Y := by
  obtain ⟨σ, hσ, hev⟩ := eventually_qForm_ge hm
  have hq : ∀ x Y : ℝ, σ * (x ^ 2 + Y ^ 2) ≤ qForm m x Y := hev.self_of_nhds
  obtain ⟨K, hK, hbound⟩ := hQ.phiFam_bound (R := ‖m‖) (norm_nonneg m) hσ
  have hc : 0 < Real.pi * σ / 2 := by positivity
  refine MeasureTheory.Integrable.mono' ((integrable_exp_neg_mul_sq hc).const_mul
    (K * Real.exp (-(Real.pi * σ / 2) * Y ^ 2))) ?_ ?_
  · exact (hQ.contDiff_x_phiFam m Y).continuous.aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun x => ?_
    calc ‖phiFam Q m x Y‖ ≤ K * Real.exp (-(Real.pi * σ / 2) * (x ^ 2 + Y ^ 2)) := hbound m le_rfl hq x Y
      _ = K * Real.exp (-(Real.pi * σ / 2) * Y ^ 2) * Real.exp (-(Real.pi * σ / 2) * x ^ 2) := by
          rw [mul_assoc, ← Real.exp_add]
          congr 2
          ring

private theorem fourier_slice_bound {P : X₄ → ℝ → ℝ → ℂ} (h : IsPoly P) (n : ℕ) :
    ∃ Pₙ : X₄ → ℝ → ℝ → ℂ, IsPoly Pₙ ∧ ∀ m : X₄, detX m ≠ 0 → ∀ Y ξ : ℝ,
      (2 * Real.pi * |ξ|) ^ n * ‖𝓕 (fun x : ℝ => phiFam P m x Y) ξ‖ ≤ ∫ x : ℝ, ‖phiFam Pₙ m x Y‖ := by
  obtain ⟨Pₙ, hPₙ, hiter⟩ := h.iteratedDeriv_x_phiFam n
  refine ⟨Pₙ, hPₙ, fun m hm Y ξ => ?_⟩
  have hint : ∀ j : ℕ, MeasureTheory.Integrable (iteratedDeriv j fun x : ℝ => phiFam P m x Y) := by
    intro j
    obtain ⟨Pj, hPj, e⟩ := h.iteratedDeriv_x_phiFam j
    rw [e m Y]
    exact hPj.integrable_phiFam hm Y
  have key := Real.fourier_iteratedDeriv (h.contDiff_x_phiFam m Y) (fun j _ => hint j) (le_top : (n : ℕ∞) ≤ ⊤)
  have hc : ‖(2 * (Real.pi : ℂ) * I * (ξ : ℂ))‖ = 2 * Real.pi * |ξ| := by
    simp [abs_of_pos Real.pi_pos]
  have h1 : ‖𝓕 (iteratedDeriv n fun x : ℝ => phiFam P m x Y) ξ‖ =
      (2 * Real.pi * |ξ|) ^ n * ‖𝓕 (fun x : ℝ => phiFam P m x Y) ξ‖ := by
    simp only [key, norm_smul, norm_pow, hc]
  calc (2 * Real.pi * |ξ|) ^ n * ‖𝓕 (fun x : ℝ => phiFam P m x Y) ξ‖
      = ‖𝓕 (iteratedDeriv n fun x : ℝ => phiFam P m x Y) ξ‖ := h1.symm
    _ ≤ ∫ x : ℝ, ‖iteratedDeriv n (fun x : ℝ => phiFam P m x Y) x‖ :=
        VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
    _ = ∫ x : ℝ, ‖phiFam Pₙ m x Y‖ := by rw [hiter m Y]

end IsPoly

private def sumFormₗ : (Fin 2 → Fin 2 → ℂ) →ₗ[ℝ] (X₄ →L[ℝ] ℂ) where
  toFun := sumForm
  map_add' c d := by
    refine ContinuousLinearMap.ext fun v => ?_
    simp only [ContinuousLinearMap.add_apply, sumForm_apply, Fin.sum_univ_two, Pi.add_apply]
    ring
  map_smul' r c := by
    refine ContinuousLinearMap.ext fun v => ?_
    simp only [ContinuousLinearMap.smul_apply, sumForm_apply, Fin.sum_univ_two, Pi.smul_apply, RingHom.id_apply,
      Complex.real_smul]
    ring

@[scoped simp] private theorem sumFormₗ_apply (c : Fin 2 → Fin 2 → ℂ) : sumFormₗ c = sumForm c := rfl

private def sumFormL : (Fin 2 → Fin 2 → ℂ) →L[ℝ] (X₄ →L[ℝ] ℂ) := LinearMap.toContinuousLinearMap sumFormₗ

@[scoped simp] private theorem sumFormL_apply (c : Fin 2 → Fin 2 → ℂ) : sumFormL c = sumForm c := rfl

private theorem smul_sumForm (a : ℂ) (c : Fin 2 → Fin 2 → ℂ) : a • sumForm c = sumForm fun i j => a * c i j := by
  refine ContinuousLinearMap.ext fun v => ?_
  simp only [ContinuousLinearMap.smul_apply, sumForm_apply, Fin.sum_univ_two, smul_eq_mul]
  ring

private theorem norm_sumForm_le (c : Fin 2 → Fin 2 → ℂ) : ‖sumForm c‖ ≤ ∑ i : Fin 2, ∑ j : Fin 2, ‖c i j‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _
    (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _) fun v => ?_
  rw [sumForm_apply, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm (‖c i j‖) (‖v‖)]
  exact mul_le_mul_of_nonneg_right (entry_abs_le_norm v i j) (norm_nonneg _)

private theorem continuous_sumForm_comp {c : ℝ → Fin 2 → Fin 2 → ℂ} (hc : ∀ i j, Continuous fun x => c x i j) :
    Continuous fun x => sumForm (c x) := by
  have h : Continuous c := continuous_pi fun i => continuous_pi fun j => hc i j
  simpa [Function.comp_def] using sumFormL.continuous.comp h

private theorem integral_sumForm {c : ℝ → Fin 2 → Fin 2 → ℂ} (hc : ∀ i j, Integrable fun x => c x i j) :
    ∫ x : ℝ, sumForm (c x) = sumForm fun i j => ∫ x : ℝ, c x i j := by
  have hci : ∀ i, Integrable fun x => c x i := fun i => integrable_pi_iff.2 fun j => hc i j
  have hint : Integrable c := integrable_pi_iff.2 hci
  have h := sumFormL.integral_comp_comm hint
  simp only [sumFormL_apply] at h
  rw [h]
  congr 1
  funext i j
  rw [eval_integral hci i, eval_integral (fun j => hc i j) j]

private theorem contDiffOn_of_sumForm_closed (𝓟 : (X₄ → ℂ) → Prop) {s : Set X₄} (hs : IsOpen s)
    (hclosed : ∀ f, 𝓟 f → ∃ D : Fin 2 → Fin 2 → X₄ → ℂ, (∀ i j, 𝓟 (D i j)) ∧
      ∀ m ∈ s, HasFDerivAt f (sumForm fun i j => D i j m) m) :
    ∀ f, 𝓟 f → ContDiffOn ℝ (⊤ : ℕ∞) f s := by
  have H : ∀ n : ℕ, ∀ f, 𝓟 f → ContDiffOn ℝ n f s := by
    intro n
    induction n with
    | zero =>
      intro f hf
      obtain ⟨D, -, hD⟩ := hclosed f hf
      rw [Nat.cast_zero, contDiffOn_zero]
      exact fun m hm => (hD m hm).continuousAt.continuousWithinAt
    | succ n ih =>
      intro f hf
      obtain ⟨D, hDP, hD⟩ := hclosed f hf
      rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen hs]
      refine ⟨fun m hm => (hD m hm).differentiableAt.differentiableWithinAt, by simp, ?_⟩
      have hDs : ContDiffOn ℝ n (fun m => sumFormL fun i j => D i j m) s :=
        sumFormL.contDiff.comp_contDiffOn
          (contDiffOn_pi.2 fun i => contDiffOn_pi.2 fun j => ih (D i j) (hDP i j))
      refine hDs.congr fun m hm => ?_
      rw [(hD m hm).fderiv, sumFormL_apply]
  intro f hf
  exact contDiffOn_infty.2 fun n => H n f hf

private def fker (ξ x : ℝ) : ℂ := Complex.exp (((-2 * Real.pi * x * ξ : ℝ) : ℂ) * I)

private theorem norm_fker (ξ x : ℝ) : ‖fker ξ x‖ = 1 := by
  rw [fker]
  exact Complex.norm_exp_ofReal_mul_I _

private theorem continuous_fker (ξ : ℝ) : Continuous (fker ξ) := by
  unfold fker
  fun_prop

private theorem fourier_eq (g : ℝ → ℂ) (ξ : ℝ) : 𝓕 g ξ = ∫ x : ℝ, fker ξ x * g x := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul, fker]

private theorem exp_split (c x Y : ℝ) :
    Real.exp (-c * (x ^ 2 + Y ^ 2)) = Real.exp (-c * Y ^ 2) * Real.exp (-c * x ^ 2) := by
  rw [← Real.exp_add]
  congr 1
  ring

private def innF (P : X₄ → ℝ → ℝ → ℂ) (m : X₄) (t : ℝ) : ℂ := ((|t|⁻¹ : ℝ) : ℂ) * 𝓕 (fun x => phiFam P m x t) t⁻¹

namespace IsPoly

private theorem integrable_fker_mul {Q : X₄ → ℝ → ℝ → ℂ} (hQ : IsPoly Q) {m : X₄} (hm : detX m ≠ 0) (Y ξ : ℝ) :
    Integrable fun x : ℝ => fker ξ x * phiFam Q m x Y := by
  refine (hQ.integrable_phiFam hm Y).norm.mono' ?_ ?_
  · exact ((continuous_fker ξ).mul (hQ.contDiff_x_phiFam m Y).continuous).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun x => ?_
    exact (show ‖fker ξ x * phiFam Q m x Y‖ = ‖phiFam Q m x Y‖ by rw [norm_mul, norm_fker, one_mul]).le

private theorem hasFDerivAt_fourier_slice {P : X₄ → ℝ → ℝ → ℂ} (h : IsPoly P) :
    ∃ D : Fin 2 → Fin 2 → X₄ → ℝ → ℝ → ℂ, (∀ i j, IsPoly (D i j)) ∧
      ∀ m₀ : X₄, detX m₀ ≠ 0 → ∀ Y ξ : ℝ,
        HasFDerivAt (fun m => 𝓕 (fun x => phiFam P m x Y) ξ)
          (sumForm fun i j => 𝓕 (fun x => phiFam (D i j) m₀ x Y) ξ) m₀ := by
  obtain ⟨D, hD, hderiv⟩ := h.hasFDerivAt_m_phiFam
  refine ⟨D, hD, fun m₀ hm₀ Y ξ => ?_⟩
  obtain ⟨σ, hσ, hev⟩ := eventually_qForm_ge hm₀
  have hnorm : ∀ᶠ m in nhds m₀, ‖m‖ < ‖m₀‖ + 1 :=
    continuous_norm.continuousAt.eventually_lt continuousAt_const (by linarith : ‖m₀‖ < ‖m₀‖ + 1)
  have hs : {m : X₄ | ‖m‖ < ‖m₀‖ + 1 ∧ ∀ x Y : ℝ, σ * (x ^ 2 + Y ^ 2) ≤ qForm m x Y} ∈ nhds m₀ := hnorm.and hev
  have hR : (0 : ℝ) ≤ ‖m₀‖ + 1 := by positivity
  choose K _hK hKb using fun i j => (hD i j).phiFam_bound hR hσ
  have hc : 0 < Real.pi * σ / 2 := by positivity
  have e : (fun m => 𝓕 (fun x => phiFam P m x Y) ξ) = fun m => ∫ x : ℝ, fker ξ x * phiFam P m x Y :=
    funext fun m => fourier_eq _ _
  rw [e]
  have hcont : Continuous fun x => sumForm fun i j => phiFam (D i j) m₀ x Y :=
    continuous_sumForm_comp fun i j => ((hD i j).contDiff_x_phiFam m₀ Y).continuous
  have hbd : ∀ᵐ x : ℝ, ∀ m ∈ {m : X₄ | ‖m‖ < ‖m₀‖ + 1 ∧ ∀ x Y : ℝ, σ * (x ^ 2 + Y ^ 2) ≤ qForm m x Y},
      ‖fker ξ x • sumForm (fun i j => phiFam (D i j) m x Y)‖ ≤ (∑ i : Fin 2, ∑ j : Fin 2, K i j)
        * Real.exp (-(Real.pi * σ / 2) * Y ^ 2) * Real.exp (-(Real.pi * σ / 2) * x ^ 2) := by
    refine Filter.Eventually.of_forall fun x m hm => ?_
    obtain ⟨hm1, hm2⟩ := hm
    rw [norm_smul, norm_fker, one_mul]
    refine (norm_sumForm_le _).trans ?_
    have hb : ∀ i j, ‖phiFam (D i j) m x Y‖ ≤
        K i j * (Real.exp (-(Real.pi * σ / 2) * Y ^ 2) * Real.exp (-(Real.pi * σ / 2) * x ^ 2)) := fun i j => by
      rw [← exp_split]
      exact hKb i j m hm1.le hm2 x Y
    simp only [Fin.sum_univ_two]
    linarith [hb 0 0, hb 0 1, hb 1 0, hb 1 1]
  have hbi : Integrable fun x : ℝ => (∑ i : Fin 2, ∑ j : Fin 2, K i j)
      * Real.exp (-(Real.pi * σ / 2) * Y ^ 2) * Real.exp (-(Real.pi * σ / 2) * x ^ 2) :=
    (integrable_exp_neg_mul_sq hc).const_mul _
  have hdf : ∀ᵐ x : ℝ, ∀ m ∈ {m : X₄ | ‖m‖ < ‖m₀‖ + 1 ∧ ∀ x Y : ℝ, σ * (x ^ 2 + Y ^ 2) ≤ qForm m x Y},
      HasFDerivAt (fun m => fker ξ x * phiFam P m x Y) (fker ξ x • sumForm fun i j => phiFam (D i j) m x Y) m :=
    Filter.Eventually.of_forall fun x m _ => (hderiv m x Y).const_mul (fker ξ x)
  refine (hasFDerivAt_integral_of_dominated_of_fderiv_le hs ?_ ?_ ?_ hbd hbi hdf).congr_fderiv ?_
  · exact Filter.Eventually.of_forall fun m =>
      ((continuous_fker ξ).mul (h.contDiff_x_phiFam m Y).continuous).aestronglyMeasurable
  · exact h.integrable_fker_mul hm₀ Y ξ
  · exact ((continuous_fker ξ).smul hcont).aestronglyMeasurable
  · simp_rw [smul_sumForm]
    rw [integral_sumForm fun i j => (hD i j).integrable_fker_mul hm₀ Y ξ]
    simp_rw [fourier_eq]

private theorem hasFDerivAt_innF {P : X₄ → ℝ → ℝ → ℂ} (h : IsPoly P) :
    ∃ D : Fin 2 → Fin 2 → X₄ → ℝ → ℝ → ℂ, (∀ i j, IsPoly (D i j)) ∧
      ∀ m₀ : X₄, detX m₀ ≠ 0 → ∀ t : ℝ,
        HasFDerivAt (fun m => innF P m t) (sumForm fun i j => innF (D i j) m₀ t) m₀ := by
  obtain ⟨D, hD, hF⟩ := h.hasFDerivAt_fourier_slice
  refine ⟨D, hD, fun m₀ hm₀ t => ?_⟩
  unfold innF
  refine ((hF m₀ hm₀ t t⁻¹).const_mul ((|t|⁻¹ : ℝ) : ℂ)).congr_fderiv ?_
  rw [smul_sumForm]

end IsPoly

section DerivEngines

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

end DerivEngines

private def AgreesWith (𝓠 : (X₄ → ℂ) → Prop) (s : Set X₄) (f : X₄ → ℂ) : Prop := ∃ q, 𝓠 q ∧ Set.EqOn f q s

private def SumFormClosed (𝓠 : (X₄ → ℂ) → Prop) (s : Set X₄) : Prop :=
  ∀ q, 𝓠 q → ∃ D : Fin 2 → Fin 2 → X₄ → ℂ, (∀ i j, 𝓠 (D i j)) ∧ ∀ m ∈ s, HasFDerivAt q (sumForm fun i j => D i j m) m

private def CombClosed (𝓠 : (X₄ → ℂ) → Prop) : Prop :=
  ∀ D : Fin 2 → Fin 2 → X₄ → ℂ, (∀ i j, 𝓠 (D i j)) → ∀ v : X₄, 𝓠 fun m => sumForm (fun i j => D i j m) v

section Engine

variable (𝓠 : (X₄ → ℂ) → Prop) {s : Set X₄}

private theorem AgreesWith.contDiffOn (hs : IsOpen s) (hclosed : SumFormClosed 𝓠 s) {f : X₄ → ℂ}
    (hf : AgreesWith 𝓠 s f) : ContDiffOn ℝ (⊤ : ℕ∞) f s := by
  obtain ⟨q, hq, hfq⟩ := hf
  exact (contDiffOn_of_sumForm_closed 𝓠 hs hclosed q hq).congr hfq

private theorem AgreesWith.fderiv_apply (hs : IsOpen s) (hclosed : SumFormClosed 𝓠 s) (hcomb : CombClosed 𝓠)
    {f : X₄ → ℂ} (hf : AgreesWith 𝓠 s f) (v : X₄) : AgreesWith 𝓠 s fun m => fderiv ℝ f m v := by
  obtain ⟨q, hq, hfq⟩ := hf
  obtain ⟨D, hD, hqD⟩ := hclosed q hq
  refine ⟨_, hcomb D hD v, fun m hm => ?_⟩
  have hEq : f =ᶠ[nhds m] q := Filter.eventuallyEq_of_mem (hs.mem_nhds hm) hfq
  show fderiv ℝ f m v = sumForm (fun i j => D i j m) v
  rw [hEq.fderiv_eq, (hqD m hm).fderiv]

private theorem AgreesWith.iteratedFDerivWithin_bound
    (hs : IsOpen s) (hclosed : SumFormClosed 𝓠 s) (hcomb : CombClosed 𝓠)
    {ι : Type} (pt : ι → X₄) (hpt : ∀ i, pt i ∈ s) (φ : ℕ → ι → ℝ) (hφ0 : ∀ n i, 0 ≤ φ n i) (hφ : Monotone φ)
    (hbound : ∀ q, 𝓠 q → ∃ (C : ℝ) (n : ℕ), ∀ i, ‖q (pt i)‖ ≤ C * φ n i) (j : ℕ) {f : X₄ → ℂ}
    (hf : AgreesWith 𝓠 s f) : ∃ (C : ℝ) (n : ℕ), ∀ i, ‖iteratedFDerivWithin ℝ j f s (pt i)‖ ≤ C * φ n i :=
  DerivEngine.iteratedFDerivWithin_bound_of_closed (Module.finBasis ℝ X₄) s hs pt hpt φ hφ0 hφ (AgreesWith 𝓠 s)
    (fun _ hg => hg.contDiffOn 𝓠 hs hclosed) (fun _ hg _ => hg.fderiv_apply 𝓠 hs hclosed hcomb _)
    (fun _ hg => by
      obtain ⟨q, hq, hgq⟩ := hg
      obtain ⟨C, n, hC⟩ := hbound q hq
      exact ⟨C, n, fun i => by rw [hgq (hpt i)]; exact hC i⟩)
    j f hf

private theorem AgreesWith.decay_top (hs : IsOpen s) (hclosed : SumFormClosed 𝓠 s) (hcomb : CombClosed 𝓠)
    {ι : Type} (pt : ι → X₄) (hpt : ∀ i, pt i ∈ s) (yof : ι → ℝ)
    (hbound : ∀ q, 𝓠 q → ∀ N : ℕ, ∃ C : ℝ, ∀ i, ‖q (pt i)‖ ≤ C * |yof i| ^ (-(N : ℝ))) (j N : ℕ) {f : X₄ → ℂ}
    (hf : AgreesWith 𝓠 s f) : ∃ C : ℝ, ∀ i, ‖iteratedFDerivWithin ℝ j f s (pt i)‖ ≤ C * |yof i| ^ (-(N : ℝ)) := by
  obtain ⟨C, -, hC⟩ := hf.iteratedFDerivWithin_bound 𝓠 hs hclosed hcomb pt hpt (fun _ i => |yof i| ^ (-(N : ℝ)))
    (fun _ i => Real.rpow_nonneg (abs_nonneg _) _) (fun _ _ _ => le_rfl)
    (fun q hq => by
      obtain ⟨C, hC⟩ := hbound q hq N
      exact ⟨C, 0, hC⟩) j
  exact ⟨C, hC⟩

private theorem AgreesWith.decay_zero (hs : IsOpen s) (hclosed : SumFormClosed 𝓠 s) (hcomb : CombClosed 𝓠)
    {ι : Type} (pt : ι → X₄) (hpt : ∀ i, pt i ∈ s) (yof : ι → ℝ) (hy0 : ∀ i, yof i ≠ 0) (hy1 : ∀ i, |yof i| ≤ 1)
    (hbound : ∀ q, 𝓠 q → ∃ (C : ℝ) (n : ℕ), ∀ i, ‖q (pt i)‖ ≤ C * |yof i| ^ (-(n : ℝ))) (j : ℕ) {f : X₄ → ℂ}
    (hf : AgreesWith 𝓠 s f) :
    ∃ (C : ℝ) (n : ℕ), ∀ i, ‖iteratedFDerivWithin ℝ j f s (pt i)‖ ≤ C * |yof i| ^ (-(n : ℝ)) :=
  hf.iteratedFDerivWithin_bound 𝓠 hs hclosed hcomb pt hpt (fun n i => |yof i| ^ (-(n : ℝ)))
    (fun _ i => Real.rpow_nonneg (abs_nonneg _) _)
    (by
      intro n n' hnn' i
      exact Real.rpow_le_rpow_of_exponent_ge (abs_pos.2 (hy0 i)) (hy1 i) (neg_le_neg (by exact_mod_cast hnn')))
    hbound j

end Engine

namespace IsPoly

private theorem continuous_xY
    {P : X₄ → ℝ → ℝ → ℂ} (h : IsPoly P) (m : X₄) : Continuous fun p : ℝ × ℝ => P m p.1 p.2 := by
  have hre : Continuous fun r : ℝ => ((r : ℝ) : ℂ) := Complex.continuous_ofReal
  induction h with
  | const c => exact continuous_const
  | rowOne j => exact continuous_const
  | rowZeroY j => exact (hre.comp continuous_snd).mul continuous_const
  | varX => exact hre.comp continuous_fst
  | varY => exact hre.comp continuous_snd
  | add _ _ ihP ihQ => exact ihP.add ihQ
  | mul _ _ ihP ihQ => exact ihP.mul ihQ

end IsPoly

private theorem continuous_gaussW_xY (m : X₄) : Continuous fun p : ℝ × ℝ => gaussW m p.1 p.2 :=
  Complex.continuous_exp.comp (isPoly_expo.continuous_xY m)

namespace IsPoly

private theorem continuous_phiFam_xY {P : X₄ → ℝ → ℝ → ℂ} (h : IsPoly P) (m : X₄) :
    Continuous fun p : ℝ × ℝ => phiFam P m p.1 p.2 :=
  (h.continuous_xY m).mul (continuous_gaussW_xY m)

private theorem measurable_innF {Q : X₄ → ℝ → ℝ → ℂ} (hQ : IsPoly Q) (m : X₄) : Measurable (innF Q m) := by
  have h1 : Measurable fun p : ℝ × ℝ => fker p.1⁻¹ p.2 := by
    unfold fker
    fun_prop
  have h2 : Measurable fun p : ℝ × ℝ => phiFam Q m p.2 p.1 :=
    ((hQ.continuous_phiFam_xY m).comp continuous_swap).measurable
  have hjoint : StronglyMeasurable fun p : ℝ × ℝ => fker p.1⁻¹ p.2 * phiFam Q m p.2 p.1 :=
    (h1.mul h2).stronglyMeasurable
  have hG : Measurable fun t : ℝ => ∫ x : ℝ, fker t⁻¹ x * phiFam Q m x t := hjoint.integral_prod_right'.measurable
  have e : innF Q m = fun t => ((|t|⁻¹ : ℝ) : ℂ) * ∫ x : ℝ, fker t⁻¹ x * phiFam Q m x t := by
    funext t
    rw [innF, fourier_eq]
  rw [e]
  exact (Complex.measurable_ofReal.comp continuous_abs.measurable.inv).mul hG

private theorem innF_bound {Q : X₄ → ℝ → ℝ → ℂ} (hQ : IsPoly Q) (n : ℕ) {R σ : ℝ} (hR : 0 ≤ R) (hσ : 0 < σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : X₄, detX m ≠ 0 → ‖m‖ ≤ R → (∀ x Y : ℝ, σ * (x ^ 2 + Y ^ 2) ≤ qForm m x Y) →
      ∀ t : ℝ, ‖innF Q m t‖ ≤ C * (|t| ^ n * |t|⁻¹) * Real.exp (-(Real.pi * σ / 2) * t ^ 2) := by
  obtain ⟨Qₙ, hQₙ, hΦ⟩ := hQ.fourier_slice_bound n
  obtain ⟨K, hK, hKb⟩ := hQₙ.phiFam_bound hR hσ
  have hc : 0 < Real.pi * σ / 2 := by positivity
  set J : ℝ := ∫ x : ℝ, Real.exp (-(Real.pi * σ / 2) * x ^ 2) with hJ
  have hJ0 : 0 ≤ J := integral_nonneg fun x => (Real.exp_pos _).le
  refine ⟨(2 * Real.pi)⁻¹ ^ n * K * J, by positivity, fun m hm hmR hq t => ?_⟩
  by_cases ht : t = 0
  · subst ht
    simp [innF]
  have hunit : ((2 * Real.pi)⁻¹ * |t|) ^ n * (2 * Real.pi * |t⁻¹|) ^ n = 1 := by
    have h3 : |t| * |t⁻¹| = 1 := by rw [← abs_mul, mul_inv_cancel₀ ht, abs_one]
    have h4 : (2 * Real.pi)⁻¹ * (2 * Real.pi) = 1 := inv_mul_cancel₀ (by positivity)
    rw [← mul_pow, show (2 * Real.pi)⁻¹ * |t| * (2 * Real.pi * |t⁻¹|) = (2 * Real.pi)⁻¹ * (2 * Real.pi) * (|t| * |t⁻¹|)
      by ring, h3, h4, one_mul, one_pow]

  have hslice : ∫ x : ℝ, ‖phiFam Qₙ m x t‖ ≤ K * Real.exp (-(Real.pi * σ / 2) * t ^ 2) * J := by
    rw [hJ, ← integral_const_mul]
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => norm_nonneg _)
      ((integrable_exp_neg_mul_sq hc).const_mul _) (Filter.Eventually.of_forall fun x => ?_)
    show ‖phiFam Qₙ m x t‖ ≤ K * Real.exp (-(Real.pi * σ / 2) * t ^ 2) * Real.exp (-(Real.pi * σ / 2) * x ^ 2)
    rw [mul_assoc, ← exp_split]
    exact hKb m hmR hq x t
  have hF : ‖𝓕 (fun x => phiFam Q m x t) t⁻¹‖ ≤
      ((2 * Real.pi)⁻¹ * |t|) ^ n * (K * Real.exp (-(Real.pi * σ / 2) * t ^ 2) * J) := by
    have h1 := hΦ m hm t t⁻¹
    calc ‖𝓕 (fun x => phiFam Q m x t) t⁻¹‖
        = ((2 * Real.pi)⁻¹ * |t|) ^ n * (2 * Real.pi * |t⁻¹|) ^ n * ‖𝓕 (fun x => phiFam Q m x t) t⁻¹‖ := by
          rw [hunit, one_mul]
      _ = ((2 * Real.pi)⁻¹ * |t|) ^ n * ((2 * Real.pi * |t⁻¹|) ^ n * ‖𝓕 (fun x => phiFam Q m x t) t⁻¹‖) :=
          mul_assoc _ _ _
      _ ≤ ((2 * Real.pi)⁻¹ * |t|) ^ n * (K * Real.exp (-(Real.pi * σ / 2) * t ^ 2) * J) :=
          mul_le_mul_of_nonneg_left (h1.trans hslice) (by positivity)
  calc ‖innF Q m t‖ = |t|⁻¹ * ‖𝓕 (fun x => phiFam Q m x t) t⁻¹‖ := by
        rw [innF, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.2 (abs_nonneg t))]
    _ ≤ |t|⁻¹ * (((2 * Real.pi)⁻¹ * |t|) ^ n * (K * Real.exp (-(Real.pi * σ / 2) * t ^ 2) * J)) :=
        mul_le_mul_of_nonneg_left hF (inv_nonneg.2 (abs_nonneg t))
    _ = (2 * Real.pi)⁻¹ ^ n * K * J * (|t| ^ n * |t|⁻¹) * Real.exp (-(Real.pi * σ / 2) * t ^ 2) := by ring

end IsPoly

private theorem chi_weight_mul {t : ℝ} (ht : t ≠ 0) (A : ℕ) :
    (|t| ^ A + |t|⁻¹ ^ A) * (|t| ^ (A + 1) * |t|⁻¹) = 1 + |t| ^ (2 * A) := by
  have h : |t| ≠ 0 := abs_ne_zero.2 ht
  have h1 : |t| ^ (A + 1) * |t|⁻¹ = |t| ^ A := by rw [pow_succ, mul_inv_cancel_right₀ h]
  have h2 : |t|⁻¹ ^ A * |t| ^ A = 1 := by rw [← mul_pow, inv_mul_cancel₀ h, one_pow]
  rw [h1, add_mul, h2]
  ring

private theorem abs_pow_le_one_add_pow (t : ℝ) (k : ℕ) : |t| ^ k ≤ 1 + t ^ (2 * k) := by
  have h2 : |t| ^ (2 * k) = t ^ (2 * k) := by rw [pow_mul, sq_abs, ← pow_mul]
  have h0 : 0 ≤ t ^ (2 * k) := by rw [← h2]; positivity
  rcases le_or_gt |t| 1 with h | h
  · have := pow_le_one₀ (abs_nonneg t) h (n := k)
    linarith
  · have := pow_le_pow_right₀ h.le (by omega : k ≤ 2 * k)
    linarith

private theorem integrable_one_add_abs_pow_mul_exp {c : ℝ} (hc : 0 < c) (k : ℕ) :
    Integrable fun t : ℝ => (1 + |t| ^ k) * Real.exp (-c * t ^ 2) := by
  have hmom : Integrable fun t : ℝ => t ^ (2 * k) * Real.exp (-c * t ^ 2) := by
    have h2k : (0 : ℝ) ≤ ((2 * k : ℕ) : ℝ) := Nat.cast_nonneg _
    have := integrable_rpow_mul_exp_neg_mul_sq hc (s := ((2 * k : ℕ) : ℝ)) (by linarith)
    simpa only [Real.rpow_natCast] using this
  have hg : Integrable fun t : ℝ => 2 * Real.exp (-c * t ^ 2) + t ^ (2 * k) * Real.exp (-c * t ^ 2) :=
    ((integrable_exp_neg_mul_sq hc).const_mul 2).add hmom
  refine hg.mono' ?_ (Filter.Eventually.of_forall fun t => ?_)
  · exact ((continuous_const.add (continuous_abs.pow k)).mul (by fun_prop)).aestronglyMeasurable
  · have hk := abs_pow_le_one_add_pow t k
    have he := Real.exp_pos (-c * t ^ 2)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right hk he.le]

private theorem ae_ne_zero : ∀ᵐ t : ℝ, t ≠ 0 := by
  have h : ∀ᵐ t : ℝ, t ∈ ({0}ᶜ : Set ℝ) := compl_mem_ae_iff.2 Real.volume_singleton
  exact h.mono fun t ht => Set.mem_compl_singleton_iff.1 ht

private def tInt (Q : X₄ → ℝ → ℝ → ℂ) (χ : ℝ → ℂ) (m : X₄) : ℂ := ∫ t : ℝ, χ t * innF Q m t

namespace IsPoly

private theorem integrable_chi_mul_innF {Q : X₄ → ℝ → ℝ → ℂ} (hQ : IsPoly Q) {m : X₄} (hm : detX m ≠ 0) {χ : ℝ → ℂ}
    (hχ : Measurable χ) {A : ℕ} (hχA : ∀ t : ℝ, t ≠ 0 → ‖χ t‖ ≤ |t| ^ A + |t|⁻¹ ^ A) :
    Integrable fun t : ℝ => χ t * innF Q m t := by
  obtain ⟨σ, hσ, hev⟩ := eventually_qForm_ge hm
  have hq : ∀ x Y : ℝ, σ * (x ^ 2 + Y ^ 2) ≤ qForm m x Y := hev.self_of_nhds
  obtain ⟨C, hC0, hCb⟩ := hQ.innF_bound (A + 1) (norm_nonneg m) hσ
  have hc : 0 < Real.pi * σ / 2 := by positivity
  refine ((integrable_one_add_abs_pow_mul_exp hc (2 * A)).const_mul C).mono'
    (hχ.mul (hQ.measurable_innF m)).aestronglyMeasurable (ae_ne_zero.mono fun t ht => ?_)
  have hw0 : 0 ≤ |t| ^ A + |t|⁻¹ ^ A := by positivity
  calc ‖χ t * innF Q m t‖ = ‖χ t‖ * ‖innF Q m t‖ := norm_mul _ _
    _ ≤ (|t| ^ A + |t|⁻¹ ^ A) * (C * (|t| ^ (A + 1) * |t|⁻¹) * Real.exp (-(Real.pi * σ / 2) * t ^ 2)) :=
        mul_le_mul (hχA t ht) (hCb m hm le_rfl hq t) (norm_nonneg _) hw0
    _ = C * ((|t| ^ A + |t|⁻¹ ^ A) * (|t| ^ (A + 1) * |t|⁻¹) * Real.exp (-(Real.pi * σ / 2) * t ^ 2)) := by ring
    _ = C * ((1 + |t| ^ (2 * A)) * Real.exp (-(Real.pi * σ / 2) * t ^ 2)) := by rw [chi_weight_mul ht]

private theorem hasFDerivAt_tInt {Q : X₄ → ℝ → ℝ → ℂ} (hQ : IsPoly Q) {χ : ℝ → ℂ} (hχ : Measurable χ) {A : ℕ}
    (hχA : ∀ t : ℝ, t ≠ 0 → ‖χ t‖ ≤ |t| ^ A + |t|⁻¹ ^ A) :
    ∃ D : Fin 2 → Fin 2 → X₄ → ℝ → ℝ → ℂ, (∀ i j, IsPoly (D i j)) ∧
      ∀ m₀ : X₄, detX m₀ ≠ 0 →
        HasFDerivAt (fun m => tInt Q χ m) (sumForm fun i j => tInt (D i j) χ m₀) m₀ := by
  obtain ⟨D, hD, hinn⟩ := hQ.hasFDerivAt_innF
  refine ⟨D, hD, fun m₀ hm₀ => ?_⟩
  simp only [tInt]
  obtain ⟨σ, hσ, hev⟩ := eventually_qForm_ge hm₀
  have hnorm : ∀ᶠ m in nhds m₀, ‖m‖ < ‖m₀‖ + 1 :=
    continuous_norm.continuousAt.eventually_lt continuousAt_const (by linarith : ‖m₀‖ < ‖m₀‖ + 1)
  have hdet : ∀ᶠ m in nhds m₀, detX m ≠ 0 := continuous_detX.continuousAt.eventually_ne hm₀
  have hs : {m : X₄ | ‖m‖ < ‖m₀‖ + 1 ∧ (∀ x Y : ℝ, σ * (x ^ 2 + Y ^ 2) ≤ qForm m x Y) ∧ detX m ≠ 0} ∈ nhds m₀ :=
    hnorm.and (hev.and hdet)
  have hR : (0 : ℝ) ≤ ‖m₀‖ + 1 := by positivity
  choose C _hC0 hCb using fun i j => (hD i j).innF_bound (A + 1) hR hσ
  have hc : 0 < Real.pi * σ / 2 := by positivity
  have hbd : ∀ᵐ t : ℝ, ∀ m ∈ {m : X₄ | ‖m‖ < ‖m₀‖ + 1 ∧ (∀ x Y : ℝ, σ * (x ^ 2 + Y ^ 2) ≤ qForm m x Y) ∧ detX m ≠ 0},
      ‖χ t • sumForm (fun i j => innF (D i j) m t)‖ ≤
        (∑ i : Fin 2, ∑ j : Fin 2, C i j) * ((1 + |t| ^ (2 * A)) * Real.exp (-(Real.pi * σ / 2) * t ^ 2)) := by
    refine ae_ne_zero.mono fun t ht m hm => ?_
    obtain ⟨hm1, hm2, hm3⟩ := hm
    have hw0 : 0 ≤ |t| ^ A + |t|⁻¹ ^ A := by positivity
    have hb : ∀ i j, ‖innF (D i j) m t‖ ≤
        C i j * (|t| ^ (A + 1) * |t|⁻¹) * Real.exp (-(Real.pi * σ / 2) * t ^ 2) := fun i j =>
      hCb i j m hm3 hm1.le hm2 t
    have hsum : ‖sumForm (fun i j => innF (D i j) m t)‖ ≤
        (∑ i : Fin 2, ∑ j : Fin 2, C i j) * ((|t| ^ (A + 1) * |t|⁻¹) * Real.exp (-(Real.pi * σ / 2) * t ^ 2)) := by
      refine (norm_sumForm_le _).trans ?_
      simp only [Fin.sum_univ_two]
      linarith [hb 0 0, hb 0 1, hb 1 0, hb 1 1]
    calc ‖χ t • sumForm (fun i j => innF (D i j) m t)‖ = ‖χ t‖ * ‖sumForm (fun i j => innF (D i j) m t)‖ :=
          norm_smul _ _
      _ ≤ (|t| ^ A + |t|⁻¹ ^ A) *
            ((∑ i : Fin 2, ∑ j : Fin 2, C i j) * ((|t| ^ (A + 1) * |t|⁻¹) * Real.exp (-(Real.pi * σ / 2) * t ^ 2))) :=
          mul_le_mul (hχA t ht) hsum (norm_nonneg _) hw0
      _ = (∑ i : Fin 2, ∑ j : Fin 2, C i j) *
            ((|t| ^ A + |t|⁻¹ ^ A) * (|t| ^ (A + 1) * |t|⁻¹) * Real.exp (-(Real.pi * σ / 2) * t ^ 2)) := by ring
      _ = (∑ i : Fin 2, ∑ j : Fin 2, C i j) * ((1 + |t| ^ (2 * A)) * Real.exp (-(Real.pi * σ / 2) * t ^ 2)) := by
          rw [chi_weight_mul ht]
  have hbi : Integrable fun t : ℝ =>
      (∑ i : Fin 2, ∑ j : Fin 2, C i j) * ((1 + |t| ^ (2 * A)) * Real.exp (-(Real.pi * σ / 2) * t ^ 2)) :=
    (integrable_one_add_abs_pow_mul_exp hc (2 * A)).const_mul _
  have hdf : ∀ᵐ t : ℝ, ∀ m ∈ {m : X₄ | ‖m‖ < ‖m₀‖ + 1 ∧ (∀ x Y : ℝ, σ * (x ^ 2 + Y ^ 2) ≤ qForm m x Y) ∧ detX m ≠ 0},
      HasFDerivAt (fun m => χ t * innF Q m t) (χ t • sumForm fun i j => innF (D i j) m t) m :=
    Filter.Eventually.of_forall fun t m hm => by
      obtain ⟨-, -, hm3⟩ := hm
      exact (hinn m hm3 t).const_mul (χ t)
  have hpi : AEStronglyMeasurable (fun t : ℝ => fun i j : Fin 2 => innF (D i j) m₀ t) volume :=
    (measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => (hD i j).measurable_innF m₀).aestronglyMeasurable
  have hsum_ae : AEStronglyMeasurable (fun t : ℝ => sumForm fun i j => innF (D i j) m₀ t) volume := by
    simpa using sumFormL.continuous.comp_aestronglyMeasurable hpi
  refine (hasFDerivAt_integral_of_dominated_of_fderiv_le hs ?_ ?_ ?_ hbd hbi hdf).congr_fderiv ?_
  · exact Filter.Eventually.of_forall fun m => (hχ.mul (hQ.measurable_innF m)).aestronglyMeasurable
  · exact hQ.integrable_chi_mul_innF hm₀ hχ hχA
  · exact hχ.aestronglyMeasurable.smul hsum_ae
  · simp_rw [smul_sumForm]
    rw [integral_sumForm fun i j => (hD i j).integrable_chi_mul_innF hm₀ hχ hχA]

end IsPoly

private def absDetPow (β : ℂ) (m : X₄) : ℂ := ((|detX m| : ℝ) : ℂ) ^ β

private theorem isEntryPoly_ofReal_mul_detX (ε : ℝ) : IsEntryPoly fun m : X₄ => ((ε * detX m : ℝ) : ℂ) :=
  (IsEntryPoly.detCoords.smul (ε : ℂ)).congr (by
    funext m
    simp [detX])

private inductive InCls (χ : ℝ → ℂ) : (X₄ → ℂ) → Prop
  | term {E : X₄ → ℂ} (hE : IsEntryPoly E) (β : ℂ) {Q : X₄ → ℝ → ℝ → ℂ} (hQ : IsPoly Q) :
      InCls χ fun m => E m * absDetPow β m * tInt Q χ m
  | add {f g : X₄ → ℂ} (hf : InCls χ f) (hg : InCls χ g) : InCls χ fun m => f m + g m
  | smul (c : ℂ) {f : X₄ → ℂ} (hf : InCls χ f) : InCls χ fun m => c * f m

namespace InCls

variable {χ : ℝ → ℂ}

private theorem congr {f g : X₄ → ℂ} (h : InCls χ f) (e : f = g) : InCls χ g := e ▸ h

private theorem combClosed : CombClosed (InCls χ) := by
  intro D hD v
  refine (((smul ((v 0 0 : ℝ) : ℂ) (hD 0 0)).add (smul ((v 0 1 : ℝ) : ℂ) (hD 0 1))).add
    ((smul ((v 1 0 : ℝ) : ℂ) (hD 1 0)).add (smul ((v 1 1 : ℝ) : ℂ) (hD 1 1)))).congr ?_
  funext m
  simp only [sumForm_apply, Fin.sum_univ_two]
  try ring

private theorem sumFormClosed (hχ : Measurable χ) {A : ℕ} (hχA : ∀ t : ℝ, t ≠ 0 → ‖χ t‖ ≤ |t| ^ A + |t|⁻¹ ^ A)
    {s : Set X₄} (hs : IsOpen s) (ε : ℝ) (hε : ∀ m ∈ s, |detX m| = ε * detX m) (hdet : ∀ m ∈ s, detX m ≠ 0) :
    SumFormClosed (InCls χ) s := by
  intro q hq
  induction hq with
  | @term E hE β Q hQ =>
    obtain ⟨DE, hDE, hE'⟩ := hE.hasFDerivAt
    obtain ⟨Db, hDb, hb'⟩ := (isEntryPoly_ofReal_mul_detX ε).hasFDerivAt
    obtain ⟨DQ, hDQ, hQ'⟩ := hQ.hasFDerivAt_tInt hχ hχA
    refine ⟨fun i j m => E m * absDetPow β m * tInt (DQ i j) χ m +
        β * (E m * Db i j m) * absDetPow (β - 1) m * tInt Q χ m + DE i j m * absDetPow β m * tInt Q χ m,
      fun i j => ((term hE β (hDQ i j)).add (term ((hE.mul (hDb i j)).smul β) (β - 1) hQ)).add (term (hDE i j) β hQ),
      fun m hm => ?_⟩
    have hpos : 0 < ε * detX m := by
      rw [← hε m hm]
      exact abs_pos.2 (hdet m hm)
    have h2 : HasFDerivAt (absDetPow β) ((β * absDetPow (β - 1) m) • sumForm fun i j => Db i j m) m := by
      by_cases hβ : β = 0
      · subst hβ
        have e : absDetPow 0 = fun _ => (1 : ℂ) := by
          funext m'
          simp [absDetPow]
        rw [e]
        refine (hasFDerivAt_const (1 : ℂ) m).congr_fderiv ?_
        refine ContinuousLinearMap.ext fun v => ?_
        simp
      obtain ⟨L, hrd⟩ : ∃ L : X₄ →L[ℝ] ℝ, HasFDerivAt (fun m : X₄ => ε * detX m) L m :=
        ⟨_, (((hasFDerivAt_coord 0 0 m).mul (hasFDerivAt_coord 1 1 m)).sub
          ((hasFDerivAt_coord 0 1 m).mul (hasFDerivAt_coord 1 0 m))).const_mul ε⟩
      have hofReal : HasFDerivAt (fun m : X₄ => ((ε * detX m : ℝ) : ℂ)) (Complex.ofRealCLM.comp L) m :=
        Complex.ofRealCLM.hasFDerivAt.comp m hrd
      have hEq : sumForm (fun i j => Db i j m) = Complex.ofRealCLM.comp L := (hb' m).unique hofReal
      have hcp : HasDerivAt (fun y : ℝ => (y : ℂ) ^ β) (β * ((ε * detX m : ℝ) : ℂ) ^ (β - 1)) (ε * detX m) :=
        hasDerivAt_ofReal_cpow_const hpos.ne' hβ
      have hcomp := hcp.hasFDerivAt.comp m hrd
      refine (hcomp.congr_of_eventuallyEq ?_).congr_fderiv ?_
      · filter_upwards [hs.mem_nhds hm] with m' hm'
        simp only [absDetPow, hε m' hm', Function.comp_apply]
      · rw [hEq]
        refine ContinuousLinearMap.ext fun v => ?_
        simp only [absDetPow, hε m hm, ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
          Complex.real_smul, ContinuousLinearMap.smul_apply, Complex.ofRealCLM_apply, smul_eq_mul]
        ring
    refine (((hE' m).mul h2).mul (hQ' m (hdet m hm))).congr_fderiv ?_
    refine ContinuousLinearMap.ext fun v => ?_
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, sumForm_apply, Fin.sum_univ_two,
      smul_eq_mul, Pi.mul_apply]
    ring
  | add _ _ ihf ihg =>
    obtain ⟨Df, hDf, hf'⟩ := ihf
    obtain ⟨Dg, hDg, hg'⟩ := ihg
    refine ⟨fun i j m => Df i j m + Dg i j m, fun i j => (hDf i j).add (hDg i j), fun m hm => ?_⟩
    refine ((hf' m hm).add (hg' m hm)).congr_fderiv ?_
    refine ContinuousLinearMap.ext fun v => ?_
    simp only [ContinuousLinearMap.add_apply, sumForm_apply, Fin.sum_univ_two]
    ring
  | smul c _ ih =>
    obtain ⟨Df, hDf, hf'⟩ := ih
    refine ⟨fun i j m => c * Df i j m, fun i j => smul c (hDf i j), fun m hm => ?_⟩
    refine ((hf' m hm).const_mul c).congr_fderiv ?_
    exact smul_sumForm c _

private theorem contDiffOn_of_agreesWith
    (hχ : Measurable χ) {A : ℕ} (hχA : ∀ t : ℝ, t ≠ 0 → ‖χ t‖ ≤ |t| ^ A + |t|⁻¹ ^ A)
    {s : Set X₄} (hs : IsOpen s) (ε : ℝ) (hε : ∀ m ∈ s, |detX m| = ε * detX m) (hdet : ∀ m ∈ s, detX m ≠ 0)
    {f : X₄ → ℂ} (hf : AgreesWith (InCls χ) s f) : ContDiffOn ℝ (⊤ : ℕ∞) f s :=
  hf.contDiffOn (InCls χ) hs (sumFormClosed hχ hχA hs ε hε hdet)

end InCls

private theorem contDiffOn_union_of_isOpen {f : X₄ → ℂ} {s t : Set X₄} (hs : IsOpen s) (ht : IsOpen t)
    (h₁ : ContDiffOn ℝ (⊤ : ℕ∞) f s) (h₂ : ContDiffOn ℝ (⊤ : ℕ∞) f t) : ContDiffOn ℝ (⊤ : ℕ∞) f (s ∪ t) := by
  refine contDiffOn_of_locally_contDiffOn fun x hx => ?_
  rcases hx with hx | hx
  · exact ⟨s, hs, hx, h₁.mono Set.inter_subset_right⟩
  · exact ⟨t, ht, hx, h₂.mono Set.inter_subset_right⟩

private theorem iteratedFDerivWithin_union_left {f : X₄ → ℂ} {s t : Set X₄} (hs : IsOpen s) (ht : IsOpen t) (j : ℕ)
    {x : X₄} (hx : x ∈ s) : iteratedFDerivWithin ℝ j f (s ∪ t) x = iteratedFDerivWithin ℝ j f s x := by
  rw [iteratedFDerivWithin_of_isOpen j (hs.union ht) (Set.mem_union_left t hx),
    iteratedFDerivWithin_of_isOpen j hs hx]

private theorem iteratedFDerivWithin_union_right {f : X₄ → ℂ} {s t : Set X₄} (hs : IsOpen s) (ht : IsOpen t) (j : ℕ)
    {x : X₄} (hx : x ∈ t) : iteratedFDerivWithin ℝ j f (s ∪ t) x = iteratedFDerivWithin ℝ j f t x := by
  rw [iteratedFDerivWithin_of_isOpen j (hs.union ht) (Set.mem_union_right s hx),
    iteratedFDerivWithin_of_isOpen j ht hx]

private structure IsGate (y : ℝ) (m : X₄) : Prop where
  y_ne : y ≠ 0
  row1 : ∀ j, |m 1 j| ≤ 1
  row0 : ∀ j, |m 0 j| ≤ |y|
  form : ∀ x t : ℝ, qForm m x t = x ^ 2 + y ^ 2 * t ^ 2
  absDet : |detX m| = |y|

namespace IsGate

variable {y : ℝ} {m : X₄}

private theorem abs_y_pos (h : IsGate y m) : 0 < |y| := abs_pos.2 h.y_ne

private theorem detX_ne (h : IsGate y m) : detX m ≠ 0 := by
  intro h0
  have h1 := h.absDet
  rw [h0, abs_zero] at h1
  exact h.y_ne (abs_eq_zero.1 h1.symm)

private theorem entries_le_abs (h : IsGate y m) (hy : 1 ≤ |y|) (i j : Fin 2) : |m i j| ≤ |y| := by
  fin_cases i
  · simpa using h.row0 j
  · simpa using (h.row1 j).trans hy

private theorem entries_le_one (h : IsGate y m) (hy : |y| ≤ 1) (i j : Fin 2) : |m i j| ≤ 1 := by
  fin_cases i
  · simpa using (h.row0 j).trans hy
  · simpa using h.row1 j

private theorem norm_absDetPow (h : IsGate y m) (β : ℂ) : ‖absDetPow β m‖ = |y| ^ β.re := by
  have hpos : 0 < |detX m| := by
    rw [h.absDet]
    exact h.abs_y_pos
  rw [absDetPow, Complex.norm_cpow_eq_rpow_re_of_pos hpos, h.absDet]

end IsGate

private theorem inv_pow_abs_eq_rpow_neg (y : ℝ) (n : ℕ) : |y|⁻¹ ^ n = |y| ^ (-(n : ℝ)) := by
  rw [Real.rpow_neg (abs_nonneg y), Real.rpow_natCast, inv_pow]

private theorem rpow_re_le_of_one_le {y : ℝ} (hy : 1 ≤ |y|) (β : ℂ) : |y| ^ β.re ≤ |y| ^ ⌈β.re⌉₊ := by
  rw [← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le hy (Nat.le_ceil _)

private theorem rpow_re_le_of_le_one {y : ℝ} (hy0 : 0 < |y|) (hy : |y| ≤ 1) (β : ℂ) :
    |y| ^ β.re ≤ |y|⁻¹ ^ ⌈-β.re⌉₊ := by
  rw [inv_pow_abs_eq_rpow_neg]
  exact Real.rpow_le_rpow_of_exponent_ge hy0 hy (by linarith [Nat.le_ceil (-β.re)])

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

private theorem abs_pow_eq_scale {y : ℝ} (hy : y ≠ 0) (t : ℝ) (j : ℕ) : |t| ^ j = |y|⁻¹ ^ j * (|y| * |t|) ^ j := by
  rw [← mul_pow, ← mul_assoc, inv_mul_cancel₀ (abs_ne_zero.2 hy), one_mul]

private theorem chi_weight_mul_general {t : ℝ} (ht : t ≠ 0) (A L : ℕ) :
    (|t| ^ A + |t|⁻¹ ^ A) * (|t| ^ (A + 1 + L) * |t|⁻¹) = |t| ^ (2 * A + L) + |t| ^ L := by
  have h : |t| ≠ 0 := abs_ne_zero.2 ht
  have h1 : |t| ^ (A + 1 + L) * |t|⁻¹ = |t| ^ (A + L) := by
    rw [show A + 1 + L = A + L + 1 by ring, pow_succ, mul_inv_cancel_right₀ h]
  have h2 : |t|⁻¹ ^ A * |t| ^ A = 1 := by rw [← mul_pow, inv_mul_cancel₀ h, one_pow]
  have h3 : |t|⁻¹ ^ A * |t| ^ (A + L) = |t| ^ L := by rw [pow_add, ← mul_assoc, h2, one_mul]
  rw [h1, add_mul, h3]
  ring

private def gateDom (k : ℕ) (s : ℝ) : ℝ := 2 * 2 ^ k * ((1 + |s| ^ k) * Real.exp (-(Real.pi / 2) * s ^ 2))

private theorem gateDom_nonneg (k : ℕ) (s : ℝ) : 0 ≤ gateDom k s := by
  unfold gateDom
  positivity

private theorem integrable_gateDom (k : ℕ) : Integrable (gateDom k) :=
  (integrable_one_add_abs_pow_mul_exp (by positivity : (0 : ℝ) < Real.pi / 2) k).const_mul _

namespace IsPoly

private theorem innF_gate_bound {Q : X₄ → ℝ → ℝ → ℂ} (hQ : IsPoly Q) (n : ℕ) :
    ∃ (C : ℝ) (d : ℕ), 0 ≤ C ∧ ∀ (y : ℝ) (m : X₄), IsGate y m → ∀ t : ℝ,
      ‖innF Q m t‖ ≤ C * (|t| ^ n * |t|⁻¹) * ((1 + |t|) ^ d * Real.exp (-(Real.pi / 2) * (y * t) ^ 2)) := by
  obtain ⟨Qₙ, hQₙ, hΦ⟩ := hQ.fourier_slice_bound n
  obtain ⟨K, d, hK, hKb⟩ := hQₙ.phiFam_gate_bound
  have hc : (0 : ℝ) < Real.pi / 2 := by positivity
  set J : ℝ := ∫ x : ℝ, Real.exp (-(Real.pi / 2) * x ^ 2) with hJ
  have hJ0 : 0 ≤ J := integral_nonneg fun x => (Real.exp_pos _).le
  refine ⟨(2 * Real.pi)⁻¹ ^ n * K * J, d, by positivity, fun y m hg t => ?_⟩
  by_cases ht : t = 0
  · subst ht
    simp [innF]
  have hunit : ((2 * Real.pi)⁻¹ * |t|) ^ n * (2 * Real.pi * |t⁻¹|) ^ n = 1 := by
    have h3 : |t| * |t⁻¹| = 1 := by rw [← abs_mul, mul_inv_cancel₀ ht, abs_one]
    have h4 : (2 * Real.pi)⁻¹ * (2 * Real.pi) = 1 := inv_mul_cancel₀ (by positivity)
    rw [← mul_pow, show (2 * Real.pi)⁻¹ * |t| * (2 * Real.pi * |t⁻¹|) = (2 * Real.pi)⁻¹ * (2 * Real.pi) * (|t| * |t⁻¹|)
      by ring, h3, h4, one_mul, one_pow]
  have hslice : ∫ x : ℝ, ‖phiFam Qₙ m x t‖ ≤ K * (1 + |t|) ^ d * Real.exp (-(Real.pi / 2) * (y * t) ^ 2) * J := by
    rw [hJ, ← integral_const_mul]
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => norm_nonneg _)
      ((integrable_exp_neg_mul_sq hc).const_mul _) (Filter.Eventually.of_forall fun x => ?_)
    show ‖phiFam Qₙ m x t‖ ≤
      K * (1 + |t|) ^ d * Real.exp (-(Real.pi / 2) * (y * t) ^ 2) * Real.exp (-(Real.pi / 2) * x ^ 2)
    rw [mul_assoc, ← exp_split]
    exact hKb m y hg.row1 hg.row0 hg.form x t
  have hF : ‖𝓕 (fun x => phiFam Q m x t) t⁻¹‖ ≤
      ((2 * Real.pi)⁻¹ * |t|) ^ n * (K * (1 + |t|) ^ d * Real.exp (-(Real.pi / 2) * (y * t) ^ 2) * J) := by
    have h1 := hΦ m hg.detX_ne t t⁻¹
    calc ‖𝓕 (fun x => phiFam Q m x t) t⁻¹‖
        = ((2 * Real.pi)⁻¹ * |t|) ^ n * (2 * Real.pi * |t⁻¹|) ^ n * ‖𝓕 (fun x => phiFam Q m x t) t⁻¹‖ := by
          rw [hunit, one_mul]
      _ = ((2 * Real.pi)⁻¹ * |t|) ^ n * ((2 * Real.pi * |t⁻¹|) ^ n * ‖𝓕 (fun x => phiFam Q m x t) t⁻¹‖) :=
          mul_assoc _ _ _
      _ ≤ ((2 * Real.pi)⁻¹ * |t|) ^ n * (K * (1 + |t|) ^ d * Real.exp (-(Real.pi / 2) * (y * t) ^ 2) * J) :=
          mul_le_mul_of_nonneg_left (h1.trans hslice) (by positivity)
  calc ‖innF Q m t‖ = |t|⁻¹ * ‖𝓕 (fun x => phiFam Q m x t) t⁻¹‖ := by
        rw [innF, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.2 (abs_nonneg t))]
    _ ≤ |t|⁻¹ * (((2 * Real.pi)⁻¹ * |t|) ^ n * (K * (1 + |t|) ^ d * Real.exp (-(Real.pi / 2) * (y * t) ^ 2) * J)) :=
        mul_le_mul_of_nonneg_left hF (inv_nonneg.2 (abs_nonneg t))
    _ = (2 * Real.pi)⁻¹ ^ n * K * J * (|t| ^ n * |t|⁻¹) *
          ((1 + |t|) ^ d * Real.exp (-(Real.pi / 2) * (y * t) ^ 2)) := by ring

private theorem tInt_gate_core {Q : X₄ → ℝ → ℝ → ℂ} (hQ : IsPoly Q) {χ : ℝ → ℂ} {A : ℕ}
    (hχA : ∀ t : ℝ, t ≠ 0 → ‖χ t‖ ≤ |t| ^ A + |t|⁻¹ ^ A) (L : ℕ) :
    ∃ (K : ℝ) (d : ℕ), 0 ≤ K ∧ ∀ (y : ℝ) (m : X₄), IsGate y m → ∀ (b : ℝ) (e : ℕ), 0 ≤ b →
      (∀ t : ℝ, 1 + |t| ≤ b * (1 + |y| * |t|)) → |y|⁻¹ ^ (2 * A + L) ≤ |y|⁻¹ ^ e → |y|⁻¹ ^ L ≤ |y|⁻¹ ^ e →
      ‖tInt Q χ m‖ ≤ K * b ^ d * |y|⁻¹ ^ (e + 1) := by
  obtain ⟨C, d, hC, hCb⟩ := hQ.innF_gate_bound (A + 1 + L)
  have hM0 : 0 ≤ ∫ s : ℝ, gateDom (2 * A + L + d) s := integral_nonneg (gateDom_nonneg _)
  refine ⟨C * ∫ s : ℝ, gateDom (2 * A + L + d) s, d, mul_nonneg hC hM0, fun y m hg b e hb hb1 h1 h2 => ?_⟩
  have hy : y ≠ 0 := hg.y_ne
  have hy0 : 0 < |y| := hg.abs_y_pos
  have hdom : Integrable fun t : ℝ => C * |y|⁻¹ ^ e * b ^ d * gateDom (2 * A + L + d) (|y| * t) :=
    ((integrable_gateDom _).comp_mul_left' hy0.ne').const_mul _
  have hpt : ∀ᵐ t : ℝ, ‖χ t * innF Q m t‖ ≤ C * |y|⁻¹ ^ e * b ^ d * gateDom (2 * A + L + d) (|y| * t) := by
    refine ae_ne_zero.mono fun t ht => ?_
    have hw := hχA t ht
    have hi := hCb y m hg t
    have hE : Real.exp (-(Real.pi / 2) * (y * t) ^ 2) = Real.exp (-(Real.pi / 2) * (|y| * t) ^ 2) := by
      rw [mul_pow, mul_pow, sq_abs]
    have hs : |(|y| * t)| = |y| * |t| := by rw [abs_mul, abs_abs]
    have hEpos : 0 < Real.exp (-(Real.pi / 2) * (|y| * t) ^ 2) := Real.exp_pos _
    have hpow1 : |t| ^ (2 * A + L) ≤ |y|⁻¹ ^ e * (|y| * |t|) ^ (2 * A + L) := by
      rw [abs_pow_eq_scale hy t (2 * A + L)]
      exact mul_le_mul_of_nonneg_right h1 (by positivity)
    have hpow2 : |t| ^ L ≤ |y|⁻¹ ^ e * (|y| * |t|) ^ L := by
      rw [abs_pow_eq_scale hy t L]
      exact mul_le_mul_of_nonneg_right h2 (by positivity)
    have hone : (1 + |t|) ^ d ≤ b ^ d * (1 + |y| * |t|) ^ d := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) (hb1 t) d
    have hprof : ((|y| * |t|) ^ (2 * A + L) + (|y| * |t|) ^ L) * (1 + |y| * |t|) ^ d *
          Real.exp (-(Real.pi / 2) * (|y| * t) ^ 2) ≤ gateDom (2 * A + L + d) (|y| * t) := by
      unfold gateDom
      rw [hs]
      calc ((|y| * |t|) ^ (2 * A + L) + (|y| * |t|) ^ L) * (1 + |y| * |t|) ^ d *
              Real.exp (-(Real.pi / 2) * (|y| * t) ^ 2)
          ≤ 2 * 2 ^ (2 * A + L + d) * (1 + (|y| * |t|) ^ (2 * A + L + d)) *
              Real.exp (-(Real.pi / 2) * (|y| * t) ^ 2) :=
            mul_le_mul_of_nonneg_right (two_pow_mul_le (by positivity) (by omega) d) hEpos.le
        _ = 2 * 2 ^ (2 * A + L + d) *
              ((1 + (|y| * |t|) ^ (2 * A + L + d)) * Real.exp (-(Real.pi / 2) * (|y| * t) ^ 2)) := by ring
    calc ‖χ t * innF Q m t‖ = ‖χ t‖ * ‖innF Q m t‖ := norm_mul _ _
      _ ≤ (|t| ^ A + |t|⁻¹ ^ A) *
            (C * (|t| ^ (A + 1 + L) * |t|⁻¹) * ((1 + |t|) ^ d * Real.exp (-(Real.pi / 2) * (y * t) ^ 2))) :=
          mul_le_mul hw hi (norm_nonneg _) (by positivity)
      _ = C * ((|t| ^ (2 * A + L) + |t| ^ L) * (1 + |t|) ^ d * Real.exp (-(Real.pi / 2) * (|y| * t) ^ 2)) := by
          rw [hE, ← chi_weight_mul_general ht A L]
          ring
      _ ≤ C * ((|y|⁻¹ ^ e * (|y| * |t|) ^ (2 * A + L) + |y|⁻¹ ^ e * (|y| * |t|) ^ L) *
            (b ^ d * (1 + |y| * |t|) ^ d) * Real.exp (-(Real.pi / 2) * (|y| * t) ^ 2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
            (mul_le_mul (add_le_add hpow1 hpow2) hone (by positivity) (by positivity)) hEpos.le) hC
      _ = C * |y|⁻¹ ^ e * b ^ d * (((|y| * |t|) ^ (2 * A + L) + (|y| * |t|) ^ L) * (1 + |y| * |t|) ^ d *
            Real.exp (-(Real.pi / 2) * (|y| * t) ^ 2)) := by ring
      _ ≤ C * |y|⁻¹ ^ e * b ^ d * gateDom (2 * A + L + d) (|y| * t) :=
          mul_le_mul_of_nonneg_left hprof (by positivity)
  show ‖∫ t : ℝ, χ t * innF Q m t‖ ≤ _
  calc ‖∫ t : ℝ, χ t * innF Q m t‖ ≤ ∫ t : ℝ, C * |y|⁻¹ ^ e * b ^ d * gateDom (2 * A + L + d) (|y| * t) :=
        norm_integral_le_of_norm_le hdom hpt
    _ = C * (∫ s : ℝ, gateDom (2 * A + L + d) s) * b ^ d * |y|⁻¹ ^ (e + 1) := by
        rw [integral_const_mul, Measure.integral_comp_mul_left (gateDom (2 * A + L + d)) (|y|), smul_eq_mul, abs_inv,
          abs_abs, pow_succ]
        generalize |y|⁻¹ = w
        ring

end IsPoly

namespace InCls

variable {χ : ℝ → ℂ}

private theorem gate_bound_top {A : ℕ} (hχA : ∀ t : ℝ, t ≠ 0 → ‖χ t‖ ≤ |t| ^ A + |t|⁻¹ ^ A) {q : X₄ → ℂ}
    (hq : InCls χ q) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (y : ℝ) (m : X₄), IsGate y m → 1 ≤ |y| → ‖q m‖ ≤ C * |y|⁻¹ ^ N := by
  induction hq with
  | @term E hE β Q hQ =>
    obtain ⟨CE, dE, hCE, hEb⟩ := hE.norm_le_of_entries_le
    obtain ⟨K, d, hK, hKb⟩ := hQ.tInt_gate_core hχA (N + dE + ⌈β.re⌉₊)
    refine ⟨CE * K, by positivity, fun y m hg hy => ?_⟩
    have hy0 : 0 < |y| := hg.abs_y_pos
    have hyi : |y|⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hy
    have h1 : ‖E m‖ ≤ CE * |y| ^ dE := hEb m (|y|) hy (hg.entries_le_abs hy)
    have h2 : ‖absDetPow β m‖ ≤ |y| ^ ⌈β.re⌉₊ := by
      rw [hg.norm_absDetPow]
      exact rpow_re_le_of_one_le hy β
    have hb1 : ∀ t : ℝ, 1 + |t| ≤ 1 * (1 + |y| * |t|) := fun t => by
      rw [one_mul]
      exact add_le_add le_rfl (le_mul_of_one_le_left (abs_nonneg t) hy)
    have h3 := hKb y m hg 1 (N + dE + ⌈β.re⌉₊) zero_le_one hb1
      (pow_le_pow_of_le_one (by positivity) hyi (by omega)) le_rfl
    rw [one_pow, mul_one] at h3
    have hw0 : 0 ≤ |y|⁻¹ := inv_nonneg.2 (abs_nonneg y)
    have hw : |y| * |y|⁻¹ = 1 := mul_inv_cancel₀ hy0.ne'
    show ‖E m * absDetPow β m * tInt Q χ m‖ ≤ CE * K * |y|⁻¹ ^ N
    revert hyi h3 hw0 hw
    generalize |y|⁻¹ = w
    intro hyi h3 hw0 hw
    have hcancel : |y| ^ dE * |y| ^ ⌈β.re⌉₊ * w ^ (N + dE + ⌈β.re⌉₊ + 1) = w ^ (N + 1) := by
      rw [show |y| ^ dE * |y| ^ ⌈β.re⌉₊ * w ^ (N + dE + ⌈β.re⌉₊ + 1) = (|y| * w) ^ (dE + ⌈β.re⌉₊) * w ^ (N + 1)
        by ring, hw, one_pow, one_mul]
    calc ‖E m * absDetPow β m * tInt Q χ m‖ = ‖E m‖ * ‖absDetPow β m‖ * ‖tInt Q χ m‖ := by
          rw [norm_mul, norm_mul]
      _ ≤ CE * |y| ^ dE * |y| ^ ⌈β.re⌉₊ * (K * w ^ (N + dE + ⌈β.re⌉₊ + 1)) :=
          mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) (by positivity)) h3 (norm_nonneg _)
            (mul_nonneg (mul_nonneg hCE (pow_nonneg (abs_nonneg y) _)) (pow_nonneg (abs_nonneg y) _))
      _ = CE * K * (|y| ^ dE * |y| ^ ⌈β.re⌉₊ * w ^ (N + dE + ⌈β.re⌉₊ + 1)) := by ring
      _ = CE * K * w ^ (N + 1) := by rw [hcancel]
      _ ≤ CE * K * w ^ N :=
          mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hw0 hyi (Nat.le_succ N)) (by positivity)
  | @add f g _ _ ihf ihg =>
    obtain ⟨C₁, hC₁, h₁⟩ := ihf
    obtain ⟨C₂, hC₂, h₂⟩ := ihg
    refine ⟨C₁ + C₂, by positivity, fun y m hg hy => ?_⟩
    show ‖f m + g m‖ ≤ (C₁ + C₂) * |y|⁻¹ ^ N
    rw [add_mul]
    exact (norm_add_le _ _).trans (add_le_add (h₁ y m hg hy) (h₂ y m hg hy))
  | @smul c f _ ih =>
    obtain ⟨C, hC, h⟩ := ih
    refine ⟨‖c‖ * C, by positivity, fun y m hg hy => ?_⟩
    show ‖c * f m‖ ≤ ‖c‖ * C * |y|⁻¹ ^ N
    rw [norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (h y m hg hy) (norm_nonneg c)

private theorem gate_bound_zero {A : ℕ} (hχA : ∀ t : ℝ, t ≠ 0 → ‖χ t‖ ≤ |t| ^ A + |t|⁻¹ ^ A) {q : X₄ → ℂ}
    (hq : InCls χ q) :
    ∃ (C : ℝ) (n : ℕ), 0 ≤ C ∧ ∀ (y : ℝ) (m : X₄), IsGate y m → |y| ≤ 1 → ‖q m‖ ≤ C * |y|⁻¹ ^ n := by
  induction hq with
  | @term E hE β Q hQ =>
    obtain ⟨CE, dE, hCE, hEb⟩ := hE.norm_le_of_entries_le
    obtain ⟨K, d, hK, hKb⟩ := hQ.tInt_gate_core hχA 0
    refine ⟨CE * K, ⌈-β.re⌉₊ + (d + (2 * A + 0 + 1)), by positivity, fun y m hg hy => ?_⟩
    have hy0 : 0 < |y| := hg.abs_y_pos
    have hyi : 1 ≤ |y|⁻¹ := (one_le_inv₀ hy0).2 hy
    have h1 : ‖E m‖ ≤ CE := by
      have h := hEb m 1 le_rfl (hg.entries_le_one hy)
      rwa [one_pow, mul_one] at h
    have h2 : ‖absDetPow β m‖ ≤ |y|⁻¹ ^ ⌈-β.re⌉₊ := by
      rw [hg.norm_absDetPow]
      exact rpow_re_le_of_le_one hy0 hy β
    have hb1 : ∀ t : ℝ, 1 + |t| ≤ |y|⁻¹ * (1 + |y| * |t|) := fun t => by
      have e : |y|⁻¹ * (1 + |y| * |t|) = |y|⁻¹ + |t| := by
        rw [mul_add, ← mul_assoc, inv_mul_cancel₀ hy0.ne', mul_one, one_mul]
      rw [e]
      exact add_le_add hyi le_rfl
    have h3 := hKb y m hg (|y|⁻¹) (2 * A + 0) (inv_nonneg.2 (abs_nonneg y)) hb1 le_rfl
      (pow_le_pow_right₀ hyi (Nat.zero_le _))
    have hw0 : 0 ≤ |y|⁻¹ := inv_nonneg.2 (abs_nonneg y)
    show ‖E m * absDetPow β m * tInt Q χ m‖ ≤ CE * K * |y|⁻¹ ^ (⌈-β.re⌉₊ + (d + (2 * A + 0 + 1)))
    revert h2 h3 hw0
    generalize |y|⁻¹ = w
    intro h2 h3 hw0
    calc ‖E m * absDetPow β m * tInt Q χ m‖ = ‖E m‖ * ‖absDetPow β m‖ * ‖tInt Q χ m‖ := by
          rw [norm_mul, norm_mul]
      _ ≤ CE * w ^ ⌈-β.re⌉₊ * (K * w ^ d * w ^ (2 * A + 0 + 1)) :=
          mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) hCE) h3 (norm_nonneg _)
            (mul_nonneg hCE (pow_nonneg hw0 _))
      _ = CE * K * w ^ (⌈-β.re⌉₊ + (d + (2 * A + 0 + 1))) := by ring
  | @add f g _ _ ihf ihg =>
    obtain ⟨C₁, n₁, hC₁, h₁⟩ := ihf
    obtain ⟨C₂, n₂, hC₂, h₂⟩ := ihg
    refine ⟨C₁ + C₂, max n₁ n₂, by positivity, fun y m hg hy => ?_⟩
    have hyi : 1 ≤ |y|⁻¹ := (one_le_inv₀ hg.abs_y_pos).2 hy
    show ‖f m + g m‖ ≤ (C₁ + C₂) * |y|⁻¹ ^ max n₁ n₂
    calc ‖f m + g m‖ ≤ ‖f m‖ + ‖g m‖ := norm_add_le _ _
      _ ≤ C₁ * |y|⁻¹ ^ n₁ + C₂ * |y|⁻¹ ^ n₂ := add_le_add (h₁ y m hg hy) (h₂ y m hg hy)
      _ ≤ C₁ * |y|⁻¹ ^ max n₁ n₂ + C₂ * |y|⁻¹ ^ max n₁ n₂ :=
          add_le_add (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hyi (le_max_left _ _)) hC₁)
            (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hyi (le_max_right _ _)) hC₂)
      _ = (C₁ + C₂) * |y|⁻¹ ^ max n₁ n₂ := (add_mul _ _ _).symm
  | @smul c f _ ih =>
    obtain ⟨C, n, hC, h⟩ := ih
    refine ⟨‖c‖ * C, n, by positivity, fun y m hg hy => ?_⟩
    show ‖c * f m‖ ≤ ‖c‖ * C * |y|⁻¹ ^ n
    rw [norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (h y m hg hy) (norm_nonneg c)

private theorem decay_top_of_agreesWith
    (hχ : Measurable χ) {A : ℕ} (hχA : ∀ t : ℝ, t ≠ 0 → ‖χ t‖ ≤ |t| ^ A + |t|⁻¹ ^ A)
    {s : Set X₄} (hs : IsOpen s) (ε : ℝ) (hε : ∀ m ∈ s, |detX m| = ε * detX m) (hdet : ∀ m ∈ s, detX m ≠ 0)
    {f : X₄ → ℂ} (hf : AgreesWith (InCls χ) s f) {ι : Type} (pt : ι → X₄) (yof : ι → ℝ) (hpt : ∀ i, pt i ∈ s)
    (hgate : ∀ i, IsGate (yof i) (pt i)) (hy : ∀ i, 1 ≤ |yof i|) (j N : ℕ) :
    ∃ C : ℝ, ∀ i, ‖iteratedFDerivWithin ℝ j f s (pt i)‖ ≤ C * |yof i| ^ (-(N : ℝ)) := by
  refine hf.decay_top (InCls χ) hs (sumFormClosed hχ hχA hs ε hε hdet) combClosed pt hpt yof ?_ j N
  intro q hq N'
  obtain ⟨C, _, hC⟩ := gate_bound_top hχA hq N'
  refine ⟨C, fun i => ?_⟩
  rw [← inv_pow_abs_eq_rpow_neg]
  exact hC (yof i) (pt i) (hgate i) (hy i)

private theorem decay_zero_of_agreesWith
    (hχ : Measurable χ) {A : ℕ} (hχA : ∀ t : ℝ, t ≠ 0 → ‖χ t‖ ≤ |t| ^ A + |t|⁻¹ ^ A)
    {s : Set X₄} (hs : IsOpen s) (ε : ℝ) (hε : ∀ m ∈ s, |detX m| = ε * detX m) (hdet : ∀ m ∈ s, detX m ≠ 0)
    {f : X₄ → ℂ} (hf : AgreesWith (InCls χ) s f) {ι : Type} (pt : ι → X₄) (yof : ι → ℝ) (hpt : ∀ i, pt i ∈ s)
    (hgate : ∀ i, IsGate (yof i) (pt i)) (hy : ∀ i, |yof i| ≤ 1) (j : ℕ) :
    ∃ (C : ℝ) (n : ℕ), ∀ i, ‖iteratedFDerivWithin ℝ j f s (pt i)‖ ≤ C * |yof i| ^ (-(n : ℝ)) := by
  refine hf.decay_zero (InCls χ) hs (sumFormClosed hχ hχA hs ε hε hdet) combClosed pt hpt yof
    (fun i => (hgate i).y_ne) hy ?_ j
  intro q hq
  obtain ⟨C, n, _, hC⟩ := gate_bound_zero hχA hq
  refine ⟨C, n, fun i => ?_⟩
  rw [← inv_pow_abs_eq_rpow_neg]
  exact hC (yof i) (pt i) (hgate i) (hy i)

end InCls

end ArchEngine
p2m_reactivate "P2MW.S_LanglandsTunnell_Converse_PrincipalFamily_exists_Wmem_ne_zero.ArchEngine"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Converse_PrincipalFamily_exists_Wmem_ne_zero.ArchEngine"

open MeasureTheory
open LanglandsTunnell.Converse.ArchR

noncomputable section

namespace ArchEngine

local notation "X₄" => (Fin 2 → Fin 2 → ℝ)

private def parityPoly (a : ZMod 2) (j : Fin 2) (m : X₄) (x Y : ℝ) : ℂ :=
  if a = 0 then 1 else ((-(Y * m 0 j + x * m 1 j) : ℝ) : ℂ)

private theorem isPoly_parityPoly (a : ZMod 2) (j : Fin 2) : IsPoly (parityPoly a j) := by
  show IsPoly fun m x Y => if a = 0 then (1 : ℂ) else ((-(Y * m 0 j + x * m 1 j) : ℝ) : ℂ)
  by_cases h : a = 0
  · simp only [if_pos h]
    exact IsPoly.const 1
  · simp only [if_neg h]
    refine IsPoly.congr
      (IsPoly.mul (IsPoly.const (-1)) (IsPoly.add (IsPoly.rowZeroY j) (IsPoly.mul IsPoly.varX (IsPoly.rowOne j)))) ?_
    funext m x Y
    simp only [Complex.ofReal_neg, Complex.ofReal_add, Complex.ofReal_mul]
    ring

private def memberPoly (a₁ a₂ : ZMod 2) : X₄ → ℝ → ℝ → ℂ := fun m x Y => parityPoly a₁ 0 m x Y * parityPoly a₂ 1 m x Y

private theorem isPoly_memberPoly (a₁ a₂ : ZMod 2) : IsPoly (memberPoly a₁ a₂) :=
  (isPoly_parityPoly a₁ 0).mul (isPoly_parityPoly a₂ 1)

private theorem psiZero_eq (a₁ a₂ : ZMod 2) (m : X₄) (x Y : ℝ) :
    TateReal.W2.psiZero a₁ a₂ (Matrix.of m) x Y = phiFam (memberPoly a₁ a₂) m x Y := by
  have key : ∀ v₀ v₁ : ℝ, ((Real.exp (-Real.pi * v₀ ^ 2) : ℝ) : ℂ) * ((Real.exp (-Real.pi * v₁ ^ 2) : ℝ) : ℂ) =
      Complex.exp (-(Real.pi : ℂ) * ((v₀ ^ 2 + v₁ ^ 2 : ℝ) : ℂ)) := by
    intro v₀ v₁
    rw [Complex.ofReal_exp, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_pow]
    ring
  simp only [TateReal.W2.psiZero, TateReal.W2.phiStd, phiFam, memberPoly, parityPoly, gaussW, expo, qForm,
    Matrix.of_apply]
  rw [mul_mul_mul_comm, key, neg_sq, neg_sq]

private theorem diagOne_one : diagOne (1 : ℝ) = 1 := by
  rw [Matrix.one_fin_two]
  rfl

private theorem innerW_eq (a₁ a₂ : ZMod 2) (m : X₄) {t : ℝ} (ht : t ≠ 0) :
    TateReal.W2.innerW a₁ a₂ (Matrix.of m) t = innF (memberPoly a₁ a₂) m t := by
  have h := TateReal.W2.innerW_diagOne a₁ a₂ (Matrix.of m) ht 1
  rw [diagOne_one, Matrix.one_mul, mul_one] at h
  have hfun : (fun x => TateReal.W2.psiZero a₁ a₂ (Matrix.of m) x t) = fun x => phiFam (memberPoly a₁ a₂) m x t :=
    funext fun x => psiZero_eq a₁ a₂ m x t
  rw [h, innF, TateReal.W3.F₁, hfun]

private theorem det_of_eq (m : X₄) : (Matrix.of m).det = detX m := by
  rw [Matrix.det_fin_two]
  rfl

private theorem asPi_Wmem_eq (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2) (m : X₄) :
    asPi (TateReal.W2.Wmem u₁ u₂ a₁ a₂) m =
      ((|detX m| : ℝ) : ℂ) * quasiChar u₁ a₁ (detX m) *
        tInt (memberPoly a₁ a₂) (quasiChar (u₁ - u₂) (a₁ + a₂)) m := by
  rw [asPi, TateReal.W2.Wmem, det_of_eq]
  congr 1
  rw [tInt]
  refine integral_congr_ae (ae_ne_zero.mono fun t ht => ?_)
  simp only [innerW_eq a₁ a₂ m ht, mul_comm]

private theorem norm_quasiChar_le (u : ℂ) (a : ZMod 2) (t : ℝ) (ht : t ≠ 0) :
    ‖quasiChar u a t‖ ≤ |t| ^ max ⌈u.re⌉₊ ⌈-u.re⌉₊ + |t|⁻¹ ^ max ⌈u.re⌉₊ ⌈-u.re⌉₊ := by
  have h0 : 0 < |t| := abs_pos.2 ht
  rw [TateReal.W2.quasiChar_eq u a t, norm_mul, TateReal.norm_sgnPow a ht, mul_one,
    Complex.norm_cpow_eq_rpow_re_of_pos h0]
  set A : ℕ := max ⌈u.re⌉₊ ⌈-u.re⌉₊
  rcases le_total 1 |t| with h1 | h1
  · calc |t| ^ u.re ≤ |t| ^ ⌈u.re⌉₊ := rpow_re_le_of_one_le h1 u
      _ ≤ |t| ^ A := pow_le_pow_right₀ h1 (le_max_left _ _)
      _ ≤ |t| ^ A + |t|⁻¹ ^ A := le_add_of_nonneg_right (by positivity)
  · calc |t| ^ u.re ≤ |t|⁻¹ ^ ⌈-u.re⌉₊ := rpow_re_le_of_le_one h0 h1 u
      _ ≤ |t|⁻¹ ^ A := pow_le_pow_right₀ ((one_le_inv₀ h0).2 h1) (le_max_right _ _)
      _ ≤ |t| ^ A + |t|⁻¹ ^ A := le_add_of_nonneg_left (by positivity)

private def posSet : Set X₄ := {m | 0 < detX m}

private def negSet : Set X₄ := {m | detX m < 0}

private theorem isOpen_posSet : IsOpen posSet := by
  unfold posSet
  exact isOpen_lt continuous_const continuous_detX

private theorem isOpen_negSet : IsOpen negSet := by
  unfold negSet
  exact isOpen_lt continuous_detX continuous_const

private theorem abs_detX_posSet : ∀ m ∈ posSet, |detX m| = 1 * detX m := fun m hm => by
  rw [abs_of_pos (show 0 < detX m from hm), one_mul]

private theorem abs_detX_negSet : ∀ m ∈ negSet, |detX m| = (-1) * detX m := fun m hm => by
  rw [abs_of_neg (show detX m < 0 from hm), neg_one_mul]

private theorem detX_ne_posSet : ∀ m ∈ posSet, detX m ≠ 0 := fun m hm => (show 0 < detX m from hm).ne'

private theorem detX_ne_negSet : ∀ m ∈ negSet, detX m ≠ 0 := fun m hm => (show detX m < 0 from hm).ne

private theorem glSet_eq : glSet = posSet ∪ negSet := by
  ext m
  simp only [glSet, posSet, negSet, Set.mem_setOf_eq, Set.mem_union, det_of_eq]
  exact ⟨fun h => (Ne.lt_or_gt h).symm, fun h => h.elim (fun h => h.ne') fun h => h.ne⟩

private theorem agreesWith_of_sgnPow (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2) {s : Set X₄} (hdet : ∀ m ∈ s, detX m ≠ 0) (c : ℂ)
    (hc : ∀ m ∈ s, TateReal.sgnPow a₁ (detX m) = c) :
    AgreesWith (InCls (quasiChar (u₁ - u₂) (a₁ + a₂))) s (asPi (TateReal.W2.Wmem u₁ u₂ a₁ a₂)) := by
  refine ⟨fun m => c * ((fun _ => (1 : ℂ)) m * absDetPow (u₁ + 1) m *
      tInt (memberPoly a₁ a₂) (quasiChar (u₁ - u₂) (a₁ + a₂)) m),
    InCls.smul c (InCls.term (IsEntryPoly.const 1) (u₁ + 1) (isPoly_memberPoly a₁ a₂)), fun m hm => ?_⟩
  have hne : ((|detX m| : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (abs_ne_zero.2 (hdet m hm))
  show asPi (TateReal.W2.Wmem u₁ u₂ a₁ a₂) m =
    c * (1 * absDetPow (u₁ + 1) m * tInt (memberPoly a₁ a₂) (quasiChar (u₁ - u₂) (a₁ + a₂)) m)
  rw [asPi_Wmem_eq, TateReal.W2.quasiChar_eq u₁ a₁ (detX m), hc m hm, absDetPow, Complex.cpow_add _ _ hne,
    Complex.cpow_one]
  ring

private theorem agreesWith_posSet (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2) :
    AgreesWith (InCls (quasiChar (u₁ - u₂) (a₁ + a₂))) posSet (asPi (TateReal.W2.Wmem u₁ u₂ a₁ a₂)) :=
  agreesWith_of_sgnPow u₁ u₂ a₁ a₂ detX_ne_posSet 1 fun m hm => by
    simp [TateReal.sgnPow, sign_pos (show 0 < detX m from hm)]

private theorem agreesWith_negSet (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2) :
    AgreesWith (InCls (quasiChar (u₁ - u₂) (a₁ + a₂))) negSet (asPi (TateReal.W2.Wmem u₁ u₂ a₁ a₂)) :=
  agreesWith_of_sgnPow u₁ u₂ a₁ a₂ detX_ne_negSet (if a₁ = 0 then 1 else -1) fun m hm => by
    simp [TateReal.sgnPow, sign_neg (show detX m < 0 from hm)]

private theorem isK_rows {k : Matrix (Fin 2) (Fin 2) ℝ} (hk : IsK k) :
    k 0 0 ^ 2 + k 0 1 ^ 2 = 1 ∧ k 1 0 ^ 2 + k 1 1 ^ 2 = 1 ∧ k 0 0 * k 1 0 + k 0 1 * k 1 1 = 0 := by
  have h : k * k.transpose = 1 := (Matrix.mem_orthogonalGroup_iff _ _).1 hk
  have h00 : (k * k.transpose) 0 0 = (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 0 := by rw [h]
  have h11 : (k * k.transpose) 1 1 = (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 1 := by rw [h]
  have h01 : (k * k.transpose) 0 1 = (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 1 := by rw [h]
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00 h11 h01
  exact ⟨by linear_combination h00, by linear_combination h11, by linear_combination h01⟩

private theorem isGate_diagOneMulCoords {y : ℝ} (hy : y ≠ 0) {k : Matrix (Fin 2) (Fin 2) ℝ} (hk : IsK k) :
    IsGate y (diagOneMulCoords y k) := by
  obtain ⟨e0, e1, e01⟩ := isK_rows hk
  obtain ⟨h00, h01, h10, h11⟩ := TateReal.W2.diagOne_mul_entries y k
  have p00 : diagOneMulCoords y k 0 0 = y * k 0 0 := by
    rw [diagOneMulCoords, Matrix.of_symm_apply, h00]
  have p01 : diagOneMulCoords y k 0 1 = y * k 0 1 := by
    rw [diagOneMulCoords, Matrix.of_symm_apply, h01]
  have p10 : diagOneMulCoords y k 1 0 = k 1 0 := by
    rw [diagOneMulCoords, Matrix.of_symm_apply, h10]
  have p11 : diagOneMulCoords y k 1 1 = k 1 1 := by
    rw [diagOneMulCoords, Matrix.of_symm_apply, h11]
  have hk00 : |k 0 0| ≤ 1 := (sq_le_one_iff_abs_le_one _).1 (by linarith [sq_nonneg (k 0 1)])
  have hk01 : |k 0 1| ≤ 1 := (sq_le_one_iff_abs_le_one _).1 (by linarith [sq_nonneg (k 0 0)])
  have hk10 : |k 1 0| ≤ 1 := (sq_le_one_iff_abs_le_one _).1 (by linarith [sq_nonneg (k 1 1)])
  have hk11 : |k 1 1| ≤ 1 := (sq_le_one_iff_abs_le_one _).1 (by linarith [sq_nonneg (k 1 0)])
  have hr00 : |y * k 0 0| ≤ |y| := by
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg y) hk00
  have hr01 : |y * k 0 1| ≤ |y| := by
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg y) hk01
  have hdp : detX (diagOneMulCoords y k) = y * detX k := by
    simp only [detX, p00, p01, p10, p11]
    ring
  have hdk : detX k = 1 ∨ detX k = -1 := by
    refine mul_self_eq_one_iff.1 ?_
    simp only [detX]
    linear_combination (k 1 0 ^ 2 + k 1 1 ^ 2) * e0 + e1 - (k 0 0 * k 1 0 + k 0 1 * k 1 1) * e01
  refine ⟨hy, ?_, ?_, ?_, ?_⟩
  · intro j
    fin_cases j
    · simpa [p10] using hk10
    · simpa [p11] using hk11
  · intro j
    fin_cases j
    · simpa [p00] using hr00
    · simpa [p01] using hr01
  · intro x Y
    exact qForm_of_orthogonal_rows (by rw [p00, p01]; linear_combination y ^ 2 * e0) (by rw [p10, p11]; exact e1)
      (by rw [p00, p01, p10, p11]; linear_combination y * e01) x Y
  · rw [hdp, abs_mul]
    rcases hdk with h | h <;> rw [h] <;> simp

private theorem ne_zero_of_one_le_abs {y : ℝ} (hy : 1 ≤ |y|) : y ≠ 0 := abs_pos.1 (zero_lt_one.trans_le hy)

section Fields

variable (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2)

private theorem wmem_smooth : ContDiffOn ℝ (⊤ : ℕ∞) (asPi (TateReal.W2.Wmem u₁ u₂ a₁ a₂)) glSet := by
  rw [glSet_eq]
  exact contDiffOn_union_of_isOpen isOpen_posSet isOpen_negSet
    (InCls.contDiffOn_of_agreesWith (TateReal.W2.measurable_quasiChar (u₁ - u₂) (a₁ + a₂))
      (norm_quasiChar_le (u₁ - u₂) (a₁ + a₂)) isOpen_posSet 1 abs_detX_posSet detX_ne_posSet
      (agreesWith_posSet u₁ u₂ a₁ a₂))
    (InCls.contDiffOn_of_agreesWith (TateReal.W2.measurable_quasiChar (u₁ - u₂) (a₁ + a₂))
      (norm_quasiChar_le (u₁ - u₂) (a₁ + a₂)) isOpen_negSet (-1) abs_detX_negSet detX_ne_negSet
      (agreesWith_negSet u₁ u₂ a₁ a₂))

private theorem wmem_decay_top : ∀ (j N : ℕ), ∃ C : ℝ, ∀ (y : ℝ) (k : Matrix (Fin 2) (Fin 2) ℝ), IsK k → 1 ≤ |y| →
    ‖iteratedFDerivWithin ℝ j (asPi (TateReal.W2.Wmem u₁ u₂ a₁ a₂)) glSet (diagOneMulCoords y k)‖ ≤
      C * |y| ^ (-(N : ℝ)) := by
  intro j N
  obtain ⟨C₁, hC₁⟩ := InCls.decay_top_of_agreesWith (TateReal.W2.measurable_quasiChar (u₁ - u₂) (a₁ + a₂))
    (norm_quasiChar_le (u₁ - u₂) (a₁ + a₂)) isOpen_posSet 1 abs_detX_posSet detX_ne_posSet
    (agreesWith_posSet u₁ u₂ a₁ a₂)
    (ι := {p : ℝ × Matrix (Fin 2) (Fin 2) ℝ // IsK p.2 ∧ 1 ≤ |p.1| ∧ diagOneMulCoords p.1 p.2 ∈ posSet})
    (fun i => diagOneMulCoords i.1.1 i.1.2) (fun i => i.1.1) (fun i => i.2.2.2)
    (fun i => isGate_diagOneMulCoords (ne_zero_of_one_le_abs i.2.2.1) i.2.1) (fun i => i.2.2.1) j N
  obtain ⟨C₂, hC₂⟩ := InCls.decay_top_of_agreesWith (TateReal.W2.measurable_quasiChar (u₁ - u₂) (a₁ + a₂))
    (norm_quasiChar_le (u₁ - u₂) (a₁ + a₂)) isOpen_negSet (-1) abs_detX_negSet detX_ne_negSet
    (agreesWith_negSet u₁ u₂ a₁ a₂)
    (ι := {p : ℝ × Matrix (Fin 2) (Fin 2) ℝ // IsK p.2 ∧ 1 ≤ |p.1| ∧ diagOneMulCoords p.1 p.2 ∈ negSet})
    (fun i => diagOneMulCoords i.1.1 i.1.2) (fun i => i.1.1) (fun i => i.2.2.2)
    (fun i => isGate_diagOneMulCoords (ne_zero_of_one_le_abs i.2.2.1) i.2.1) (fun i => i.2.2.1) j N
  refine ⟨max C₁ C₂, fun y k hk hy => ?_⟩
  have hg := isGate_diagOneMulCoords (ne_zero_of_one_le_abs hy) hk
  have hr : 0 ≤ |y| ^ (-(N : ℝ)) := Real.rpow_nonneg (abs_nonneg y) _
  rw [glSet_eq]
  rcases hg.detX_ne.lt_or_gt with hneg | hpos
  · rw [iteratedFDerivWithin_union_right isOpen_posSet isOpen_negSet j
      (show diagOneMulCoords y k ∈ negSet from hneg)]
    exact (hC₂ ⟨(y, k), hk, hy, hneg⟩).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hr)
  · rw [iteratedFDerivWithin_union_left isOpen_posSet isOpen_negSet j
      (show diagOneMulCoords y k ∈ posSet from hpos)]
    exact (hC₁ ⟨(y, k), hk, hy, hpos⟩).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hr)

private theorem wmem_decay_zero
    : ∀ j : ℕ, ∃ (C σ : ℝ), ∀ (y : ℝ) (k : Matrix (Fin 2) (Fin 2) ℝ), IsK k → y ≠ 0 → |y| ≤ 1 →
    ‖iteratedFDerivWithin ℝ j (asPi (TateReal.W2.Wmem u₁ u₂ a₁ a₂)) glSet (diagOneMulCoords y k)‖ ≤
      C * |y| ^ (-σ) := by
  intro j
  obtain ⟨C₁, n₁, hC₁⟩ := InCls.decay_zero_of_agreesWith (TateReal.W2.measurable_quasiChar (u₁ - u₂) (a₁ + a₂))
    (norm_quasiChar_le (u₁ - u₂) (a₁ + a₂)) isOpen_posSet 1 abs_detX_posSet detX_ne_posSet
    (agreesWith_posSet u₁ u₂ a₁ a₂)
    (ι := {p : ℝ × Matrix (Fin 2) (Fin 2) ℝ // IsK p.2 ∧ p.1 ≠ 0 ∧ |p.1| ≤ 1 ∧ diagOneMulCoords p.1 p.2 ∈ posSet})
    (fun i => diagOneMulCoords i.1.1 i.1.2) (fun i => i.1.1) (fun i => i.2.2.2.2)
    (fun i => isGate_diagOneMulCoords i.2.2.1 i.2.1) (fun i => i.2.2.2.1) j
  obtain ⟨C₂, n₂, hC₂⟩ := InCls.decay_zero_of_agreesWith (TateReal.W2.measurable_quasiChar (u₁ - u₂) (a₁ + a₂))
    (norm_quasiChar_le (u₁ - u₂) (a₁ + a₂)) isOpen_negSet (-1) abs_detX_negSet detX_ne_negSet
    (agreesWith_negSet u₁ u₂ a₁ a₂)
    (ι := {p : ℝ × Matrix (Fin 2) (Fin 2) ℝ // IsK p.2 ∧ p.1 ≠ 0 ∧ |p.1| ≤ 1 ∧ diagOneMulCoords p.1 p.2 ∈ negSet})
    (fun i => diagOneMulCoords i.1.1 i.1.2) (fun i => i.1.1) (fun i => i.2.2.2.2)
    (fun i => isGate_diagOneMulCoords i.2.2.1 i.2.1) (fun i => i.2.2.2.1) j
  refine ⟨max (max C₁ C₂) 0, ((max n₁ n₂ : ℕ) : ℝ), fun y k hk hy0 hy1 => ?_⟩
  have hg := isGate_diagOneMulCoords hy0 hk
  have hC0 : (0 : ℝ) ≤ max (max C₁ C₂) 0 := le_max_right _ _
  have hmono : ∀ n : ℕ, n ≤ max n₁ n₂ → |y| ^ (-(n : ℝ)) ≤ |y| ^ (-((max n₁ n₂ : ℕ) : ℝ)) := fun n hn =>
    Real.rpow_le_rpow_of_exponent_ge (abs_pos.2 hy0) hy1 (neg_le_neg (Nat.cast_le.2 hn))
  rw [glSet_eq]
  rcases hg.detX_ne.lt_or_gt with hneg | hpos
  · rw [iteratedFDerivWithin_union_right isOpen_posSet isOpen_negSet j (show diagOneMulCoords y k ∈ negSet from hneg)]
    calc ‖iteratedFDerivWithin ℝ j (asPi (TateReal.W2.Wmem u₁ u₂ a₁ a₂)) negSet (diagOneMulCoords y k)‖
        ≤ C₂ * |y| ^ (-(n₂ : ℝ)) := hC₂ ⟨(y, k), hk, hy0, hy1, hneg⟩
      _ ≤ max (max C₁ C₂) 0 * |y| ^ (-(n₂ : ℝ)) :=
          mul_le_mul_of_nonneg_right ((le_max_right C₁ C₂).trans (le_max_left _ _)) (Real.rpow_nonneg (abs_nonneg y) _)
      _ ≤ max (max C₁ C₂) 0 * |y| ^ (-((max n₁ n₂ : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left (hmono n₂ (le_max_right _ _)) hC0
  · rw [iteratedFDerivWithin_union_left isOpen_posSet isOpen_negSet j (show diagOneMulCoords y k ∈ posSet from hpos)]
    calc ‖iteratedFDerivWithin ℝ j (asPi (TateReal.W2.Wmem u₁ u₂ a₁ a₂)) posSet (diagOneMulCoords y k)‖
        ≤ C₁ * |y| ^ (-(n₁ : ℝ)) := hC₁ ⟨(y, k), hk, hy0, hy1, hpos⟩
      _ ≤ max (max C₁ C₂) 0 * |y| ^ (-(n₁ : ℝ)) :=
          mul_le_mul_of_nonneg_right ((le_max_left C₁ C₂).trans (le_max_left _ _)) (Real.rpow_nonneg (abs_nonneg y) _)
      _ ≤ max (max C₁ C₂) 0 * |y| ^ (-((max n₁ n₂ : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left (hmono n₁ (le_max_left _ _)) hC0

end Fields
p2m_reactivate "P2MW.S_LanglandsTunnell_Converse_PrincipalFamily_exists_Wmem_ne_zero.ArchEngine"

end ArchEngine
p2m_reactivate "P2MW.S_LanglandsTunnell_Converse_PrincipalFamily_exists_Wmem_ne_zero.ArchEngine"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Converse_PrincipalFamily_exists_Wmem_ne_zero.ArchEngine"

private theorem wmem_bridge (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2) :
    LanglandsTunnell.Converse.PrincipalFamily.Wmem u₁ u₂ a₁ a₂ = TateReal.W2.Wmem u₁ u₂ a₁ a₂ := rfl

open LanglandsTunnell.Converse.PrincipalFamily LanglandsTunnell LanglandsTunnell.Converse in

theorem solution (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2) :
    ∃ g : GL (Fin 2) ℝ, Wmem u₁ u₂ a₁ a₂ (g : Matrix (Fin 2) (Fin 2) ℝ) ≠ 0 :=
  by
    rw [wmem_bridge]
    exact TateReal.W2.exists_Wmem_GL_ne_zero u₁ u₂ a₁ a₂

end S_LanglandsTunnell_Converse_PrincipalFamily_exists_Wmem_ne_zero
end P2MW
export P2MW.S_LanglandsTunnell_Converse_PrincipalFamily_exists_Wmem_ne_zero (solution)
