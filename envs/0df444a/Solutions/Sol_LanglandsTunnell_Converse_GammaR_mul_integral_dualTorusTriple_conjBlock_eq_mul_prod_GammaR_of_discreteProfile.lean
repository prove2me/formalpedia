-- Prove2me | solution 1 for LanglandsTunnell.Converse.GammaR_mul_integral_dualTorusTriple_conjBlock_eq_mul_prod_GammaR_of_discreteProfile
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/4cb04a84-be30-5cac-91ae-493a976a3a0c

import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3
import Definitions.Def_AutomorphicForm_ArchWeightChar
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Theorems.Thm_LanglandsTunnell_integral_prod_eq_setIntegral_Ioi_setIntegral_Ioi_sum_reflections
import Theorems.Thm_LanglandsTunnell_integral_mulConvGaussian_torusGauss_eq_GammaR_prod_div_of_balance
import Theorems.Thm_LanglandsTunnell_integral_mulConvGaussian_torusGauss_two_term_eq_GammaR_prod_div
import Theorems.Thm_LanglandsTunnell_Converse_exists_forall_integrable_dualQuadruple_and_torusTriple_conjBlock_of_mulConvGaussian_sheets
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_Converse_GammaR_mul_integral_dualTorusTriple_conjBlock_eq_mul_prod_GammaR_of_discreteProfile

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse MeasureTheory

noncomputable section

namespace P2mKcDualEvalFlatDisc

open Real Set

theorem ofReal_cpow_eq_exp {x : ℝ} (hx : 0 < x) (z : ℂ) :
    ((x : ℝ) : ℂ) ^ z = Complex.exp (z * ((Real.log x : ℝ) : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.2 hx.ne'), Complex.ofReal_log hx.le, mul_comm]

theorem ofReal_eq_exp_log {x : ℝ} (hx : 0 < x) : ((x : ℝ) : ℂ) = Complex.exp ((Real.log x : ℝ) : ℂ) := by
  rw [← Complex.ofReal_exp, Real.exp_log hx]

theorem quasiChar_of_pos (u : ℂ) (a : ZMod 2) {x : ℝ} (hx : 0 < x) : ArchR.quasiChar u a x = ((x : ℝ) : ℂ) ^ u := by
  unfold ArchR.quasiChar
  rw [abs_of_pos hx]
  split_ifs
  · rw [mul_one]
  · rw [sign_pos hx]; simp

theorem quasiChar_neg (u : ℂ) (a : ZMod 2) (x : ℝ) (hx : x ≠ 0) :
    ArchR.quasiChar u a (-x) = (-1 : ℂ) ^ a.val * ArchR.quasiChar u a x := by
  unfold ArchR.quasiChar
  rw [abs_neg]
  have ha : a = 0 ∨ a = 1 := (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) a
  rcases ha with h | h
  · subst h; simp
  · subst h
    simp only [one_ne_zero, if_false, ZMod.val_one, pow_one, Left.sign_neg, SignType.coe_neg]
    push_cast
    ring

theorem quasiChar_zero_pos (a : ZMod 2) {x : ℝ} (hx : 0 < x) : ArchR.quasiChar 0 a x = 1 := by
  rw [quasiChar_of_pos _ _ hx, Complex.cpow_zero]

theorem v0 : (0 : ZMod 2).val = 0 := rfl
theorem v1 : (1 : ZMod 2).val = 1 := rfl

def E (y t : ℝ) : ℝ := rexp (-(π * (t - y / t) ^ 2))

theorem E_pos (y t : ℝ) : 0 < E y t := exp_pos _

theorem measurable_E (y : ℝ) : Measurable (E y) := by
  unfold E; fun_prop

theorem image_sub_div {y : ℝ} (hy : 0 < y) : (fun t : ℝ => t - y / t) '' Ioi 0 = univ := by
  refine eq_univ_of_forall fun u => ?_
  set S : ℝ := √(u ^ 2 + 4 * y) with hS
  have hS0 : 0 ≤ u ^ 2 + 4 * y := by positivity
  have hSsq : S ^ 2 = u ^ 2 + 4 * y := by rw [hS, sq_sqrt hS0]
  have hSpos : 0 < S := by rw [hS]; exact sqrt_pos.2 (by positivity)
  have hSu : |u| < S := by
    rw [hS, ← sqrt_sq_eq_abs]
    exact sqrt_lt_sqrt (sq_nonneg u) (by linarith)
  have ht : 0 < (u + S) / 2 := by
    have := neg_abs_le u
    linarith
  refine ⟨(u + S) / 2, ht, ?_⟩
  have ht0 : (u + S) / 2 ≠ 0 := ht.ne'
  have h2 : y / ((u + S) / 2) = (u + S) / 2 - u := by
    rw [div_eq_iff ht0]
    linear_combination (-1 / 4 : ℝ) * hSsq
  simp only
  linarith [h2]

theorem strictMonoOn_sub_div {y : ℝ} (hy : 0 < y) : StrictMonoOn (fun t : ℝ => t - y / t) (Ioi 0) := by
  intro a ha b hb hab
  have : y / b < y / a := div_lt_div_of_pos_left hy ha hab
  simp only
  linarith

theorem hasDerivAt_sub_div (y : ℝ) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun t : ℝ => t - y / t) (1 + y / t ^ 2) t := by
  have h1 : HasDerivAt (fun t : ℝ => y * t⁻¹) (y * (-(t ^ 2)⁻¹)) t := (hasDerivAt_inv ht).const_mul y
  have h2 := (hasDerivAt_id t).sub h1
  convert h2 using 1
  · rfl
  · rfl
  · rfl
  field_simp
  ring

theorem hasDerivAt_div (y : ℝ) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun t : ℝ => y / t) (-(y / t ^ 2)) t := by
  have h1 : HasDerivAt (fun t : ℝ => y * t⁻¹) (y * (-(t ^ 2)⁻¹)) t := (hasDerivAt_inv ht).const_mul y
  convert h1 using 1 <;> first | rfl | ring1 | (field_simp; done)

theorem image_div {y : ℝ} (hy : 0 < y) : (fun t : ℝ => y / t) '' Ioi 0 = Ioi 0 := by
  ext t
  constructor
  · rintro ⟨r, hr, rfl⟩; exact div_pos hy hr
  · intro ht
    exact ⟨y / t, div_pos hy ht, by field_simp⟩

theorem injOn_div {y : ℝ} (hy : 0 < y) : InjOn (fun t : ℝ => y / t) (Ioi 0) := by
  intro a ha b hb hab
  simp only at hab
  have ha0 : (a : ℝ) ≠ 0 := ne_of_gt ha
  have hb0 : (b : ℝ) ≠ 0 := ne_of_gt hb
  field_simp at hab
  nlinarith [hab]

theorem integral_W {y : ℝ} (hy : 0 < y) : ∫ t in Ioi (0:ℝ), (1 + y / t ^ 2) * E y t = 1 := by
  have h := MeasureTheory.integral_image_eq_integral_abs_deriv_smul (s := Ioi (0:ℝ))
    (f := fun t : ℝ => t - y / t) (f' := fun t => 1 + y / t ^ 2) measurableSet_Ioi
    (fun t ht => (hasDerivAt_sub_div y (ne_of_gt ht)).hasDerivWithinAt) (strictMonoOn_sub_div hy).injOn
    (fun u => rexp (-(π * u ^ 2)))
  have hg : ∫ u : ℝ, rexp (-(π * u ^ 2)) = 1 := by
    have := integral_gaussian π
    simp only [neg_mul] at this
    rw [this, div_self pi_ne_zero, sqrt_one]
  have h' : ∫ x in Ioi (0:ℝ), |1 + y / x ^ 2| • rexp (-(π * (x - y / x) ^ 2)) = 1 := by
    rw [← h, image_sub_div hy, Measure.restrict_univ, hg]
  refine Eq.trans ?_ h'
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have hpos : 0 < 1 + y / t ^ 2 := by positivity
  simp only [E, smul_eq_mul, abs_of_pos hpos]

theorem integral_E_eq {y : ℝ} (hy : 0 < y) :
    ∫ t in Ioi (0:ℝ), E y t = ∫ t in Ioi (0:ℝ), y / t ^ 2 * E y t := by
  have h := MeasureTheory.integral_image_eq_integral_abs_deriv_smul (s := Ioi (0:ℝ))
    (f := fun t : ℝ => y / t) (f' := fun t => -(y / t ^ 2)) measurableSet_Ioi
    (fun t ht => (hasDerivAt_div y (ne_of_gt ht)).hasDerivWithinAt) (injOn_div hy) (E y)
  rw [image_div hy] at h
  rw [h]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht0 : (t : ℝ) ≠ 0 := ne_of_gt ht
  have hpos : 0 ≤ y / t ^ 2 := by positivity
  simp only [smul_eq_mul, abs_neg, abs_of_nonneg hpos, E]
  congr 2
  rw [div_div_cancel₀ hy.ne']
  ring

theorem integral_P {y : ℝ} (hy : 0 < y) : ∫ t in Ioi (0:ℝ), y / t ^ 2 * E y t = 1 / 2 := by
  have hW := integral_W hy
  have hWint : IntegrableOn (fun t => (1 + y / t ^ 2) * E y t) (Ioi 0) :=
    integrable_of_integral_eq_one hW
  have hmeasP : AEStronglyMeasurable (fun t => y / t ^ 2 * E y t) (volume.restrict (Ioi (0:ℝ))) := by
    have : Measurable (fun t => y / t ^ 2 * E y t) := by
      have := measurable_E y; fun_prop
    exact this.aestronglyMeasurable
  have hmeasE : AEStronglyMeasurable (E y) (volume.restrict (Ioi (0:ℝ))) := (measurable_E y).aestronglyMeasurable
  have hPint : IntegrableOn (fun t => y / t ^ 2 * E y t) (Ioi 0) := by
    refine Integrable.mono' hWint hmeasP (Filter.Eventually.of_forall fun t => ?_)
    have h1 : 0 ≤ y / t ^ 2 := by positivity
    have h2 : 0 < E y t := E_pos y t
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h1 h2.le)]
    nlinarith
  have hEint : IntegrableOn (E y) (Ioi 0) := by
    refine Integrable.mono' hWint hmeasE (Filter.Eventually.of_forall fun t => ?_)
    have h1 : 0 ≤ y / t ^ 2 := by positivity
    have h2 : 0 < E y t := E_pos y t
    rw [Real.norm_eq_abs, abs_of_nonneg h2.le]
    nlinarith
  have hsplit : ∫ t in Ioi (0:ℝ), (1 + y / t ^ 2) * E y t =
      (∫ t in Ioi (0:ℝ), E y t) + ∫ t in Ioi (0:ℝ), y / t ^ 2 * E y t := by
    rw [← integral_add hEint hPint]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    ring
  rw [hW, integral_E_eq hy] at hsplit
  linarith

theorem glasser {y : ℝ} (hy : 0 < y) :
    ∫ t in Ioi (0:ℝ), y / t * rexp (-(π * t ^ 2)) * rexp (-(π * (y / t) ^ 2)) / t = rexp (-(2 * π * y)) / 2 := by
  have h1 : ∫ t in Ioi (0:ℝ), y / t * rexp (-(π * t ^ 2)) * rexp (-(π * (y / t) ^ 2)) / t =
      ∫ t in Ioi (0:ℝ), (y / t ^ 2 * E y t) * rexp (-(2 * π * y)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : (t : ℝ) ≠ 0 := ne_of_gt ht
    simp only [E]
    rw [show y / t * rexp (-(π * t ^ 2)) * rexp (-(π * (y / t) ^ 2)) / t =
      y / t ^ 2 * (rexp (-(π * t ^ 2)) * rexp (-(π * (y / t) ^ 2))) by field_simp]
    rw [mul_assoc, ← Real.exp_add, ← Real.exp_add]
    congr 2
    field_simp
    ring
  rw [h1, integral_mul_const, integral_P hy]
  ring

theorem discrete_eq (γ₀ : ℂ) {y : ℝ} (hy : 0 < y) :
    (4 : ℂ) * ∫ t in Ioi (0:ℝ),
        ((t : ℂ) ^ γ₀ * (Real.exp (-(Real.pi * t ^ 2)) : ℂ)) *
          (((y / t : ℝ) : ℂ) ^ (γ₀ + 1) * (Real.exp (-(Real.pi * (y / t) ^ 2)) : ℂ)) / (t : ℂ)
      = (2 : ℂ) * ((y : ℂ) ^ γ₀ * ((Real.exp (-(2 * Real.pi * y)) : ℝ) : ℂ)) := by
  have hcongr : ∀ t ∈ Ioi (0:ℝ),
      ((t : ℂ) ^ γ₀ * (Real.exp (-(Real.pi * t ^ 2)) : ℂ)) *
          (((y / t : ℝ) : ℂ) ^ (γ₀ + 1) * (Real.exp (-(Real.pi * (y / t) ^ 2)) : ℂ)) / (t : ℂ)
        = (y : ℂ) ^ γ₀ * ((y / t * rexp (-(π * t ^ 2)) * rexp (-(π * (y / t) ^ 2)) / t : ℝ) : ℂ) := by
    intro t ht
    have ht' : (0:ℝ) < t := ht
    have hyt : (0:ℝ) < y / t := div_pos hy ht'
    have hne : ((y / t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hyt.ne'
    have hcp : (t : ℂ) ^ γ₀ * ((y / t : ℝ) : ℂ) ^ (γ₀ + 1) = (y : ℂ) ^ γ₀ * ((y / t : ℝ) : ℂ) := by
      rw [Complex.cpow_add _ _ hne, Complex.cpow_one, ← mul_assoc,
        ← Complex.mul_cpow_ofReal_nonneg ht'.le hyt.le, ← Complex.ofReal_mul, mul_div_cancel₀ _ ht'.ne']
    calc ((t : ℂ) ^ γ₀ * (Real.exp (-(Real.pi * t ^ 2)) : ℂ)) *
          (((y / t : ℝ) : ℂ) ^ (γ₀ + 1) * (Real.exp (-(Real.pi * (y / t) ^ 2)) : ℂ)) / (t : ℂ)
        = ((t : ℂ) ^ γ₀ * ((y / t : ℝ) : ℂ) ^ (γ₀ + 1)) *
            ((Real.exp (-(Real.pi * t ^ 2)) : ℂ) * (Real.exp (-(Real.pi * (y / t) ^ 2)) : ℂ) / (t : ℂ)) := by ring
      _ = (y : ℂ) ^ γ₀ * ((y / t * rexp (-(π * t ^ 2)) * rexp (-(π * (y / t) ^ 2)) / t : ℝ) : ℂ) := by
        rw [hcp]; push_cast; ring
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr, integral_const_mul, integral_complex_ofReal, glasser hy]
  push_cast
  ring

theorem mulConv_symm (α β : ℂ) (y : ℝ) (hy : 0 < y) :
    (4 : ℂ) * ∫ r in Ioi (0:ℝ),
        ((r : ℂ) ^ α * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
          ((((y) / r : ℝ) : ℂ) ^ β * (Real.exp (-(Real.pi * ((y) / r) ^ 2)) : ℂ)) / (r : ℂ)
      = (4 : ℂ) * ∫ r in Ioi (0:ℝ),
        ((r : ℂ) ^ β * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
          ((((y) / r : ℝ) : ℂ) ^ α * (Real.exp (-(Real.pi * ((y) / r) ^ 2)) : ℂ)) / (r : ℂ) := by
  congr 1
  have h := MeasureTheory.integral_image_eq_integral_abs_deriv_smul (s := Ioi (0:ℝ))
    (f := fun t : ℝ => y / t) (f' := fun t => -(y / t ^ 2)) measurableSet_Ioi
    (fun t ht => (hasDerivAt_div y (ne_of_gt ht)).hasDerivWithinAt) (injOn_div hy)
    (fun r : ℝ => ((r : ℂ) ^ β * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
          ((((y) / r : ℝ) : ℂ) ^ α * (Real.exp (-(Real.pi * ((y) / r) ^ 2)) : ℂ)) / (r : ℂ))
  rw [image_div hy] at h
  rw [h]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht' : (0:ℝ) < t := ht
  have ht0 : (t : ℝ) ≠ 0 := ne_of_gt ht
  have hyt : (0:ℝ) < y / t := div_pos hy ht'
  have hpos : 0 ≤ y / t ^ 2 := by positivity
  have e1 : y / (y / t) = t := by field_simp
  simp only [abs_neg, abs_of_nonneg hpos, e1, Complex.real_smul]
  have hc1 : ((y / t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hyt.ne'
  have hc2 : ((t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ht0
  have hc3 : ((y : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have e2 : ((y / t ^ 2 : ℝ) : ℂ) = ((y : ℝ) : ℂ) / (((t : ℝ) : ℂ) * ((t : ℝ) : ℂ)) := by push_cast; ring
  rw [e2]
  have e3 : ((y / t : ℝ) : ℂ) = ((y : ℝ) : ℂ) / ((t : ℝ) : ℂ) := by push_cast; ring
  rw [e3]
  field_simp

theorem iter_eq_prod (F : ℝ → ℝ → ℝ → ℂ)
    (hFint : Integrable (fun x : ℝ × ℝ × ℝ => F x.1 x.2.1 x.2.2)
      ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ioi 0))))) :
    (∫ t : ℝ, ∫ q : ℝ, ∫ p in Set.Ioi (0 : ℝ), F t q p) =
      ∫ x, F x.1 x.2.1 x.2.2 ∂((volume : Measure ℝ).prod ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ioi 0)))) := by
  rw [integral_prod (f := fun x : ℝ × ℝ × ℝ => F x.1 x.2.1 x.2.2) hFint]
  refine integral_congr_ae ?_
  filter_upwards [hFint.prod_right_ae] with t ht
  exact (integral_prod (f := fun yz : ℝ × ℝ => F t yz.1 yz.2) ht).symm

theorem fold3 (F H : ℝ → ℝ → ℝ → ℂ) (C : ℂ)
    (hFint : Integrable (fun x : ℝ × ℝ × ℝ => F x.1 x.2.1 x.2.2)
      ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ioi 0)))))
    (key : ∀ t q p : ℝ, 0 < t → 0 < q → 0 < p →
      F t q p + F (-t) q p + F t (-q) p + F (-t) (-q) p = C * H t q p) :
    ∫ x, F x.1 x.2.1 x.2.2 ∂((volume : Measure ℝ).prod ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ioi 0)))) =
      C * ∫ t in Set.Ioi (0 : ℝ), ∫ p in Set.Ioi (0 : ℝ), ∫ q in Set.Ioi (0 : ℝ), H t q p := by
  set ν : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ioi 0) with hν

  have hΦ : MeasurePreserving (⇑(MeasurableEquiv.prodAssoc : (ℝ × ℝ) × ℝ ≃ᵐ ℝ × ℝ × ℝ))
      (((volume : Measure ℝ).prod (volume : Measure ℝ)).prod ν) ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod ν)) :=
    measurePreserving_prodAssoc _ _ _
  have hFa : Integrable ((fun x : ℝ × ℝ × ℝ => F x.1 x.2.1 x.2.2) ∘ ⇑(MeasurableEquiv.prodAssoc : (ℝ × ℝ) × ℝ ≃ᵐ ℝ × ℝ × ℝ))
      (((volume : Measure ℝ).prod (volume : Measure ℝ)).prod ν) :=
    (hΦ.integrable_comp hFint.aestronglyMeasurable).2 hFint
  have step0 : ∫ x, F x.1 x.2.1 x.2.2 ∂((volume : Measure ℝ).prod ((volume : Measure ℝ).prod ν)) =
      ∫ pr : (ℝ × ℝ) × ℝ, F pr.1.1 pr.1.2 pr.2 ∂(((volume : Measure ℝ).prod (volume : Measure ℝ)).prod ν) := by
    rw [← hΦ.integral_comp (MeasurableEquiv.prodAssoc).measurableEmbedding]
    rfl
  have step1 : ∫ pr : (ℝ × ℝ) × ℝ, F pr.1.1 pr.1.2 pr.2 ∂(((volume : Measure ℝ).prod (volume : Measure ℝ)).prod ν) =
      ∫ pq : ℝ × ℝ, (∫ p, F pq.1 pq.2 p ∂ν) ∂((volume : Measure ℝ).prod (volume : Measure ℝ)) :=
    integral_prod (f := fun pr : (ℝ × ℝ) × ℝ => F pr.1.1 pr.1.2 pr.2) hFa
  have hh : Integrable (fun pq : ℝ × ℝ => ∫ p, F pq.1 pq.2 p ∂ν) ((volume : Measure ℝ).prod (volume : Measure ℝ)) :=
    hFa.integral_prod_left
  have step2 := LanglandsTunnell.integral_prod_eq_setIntegral_Ioi_setIntegral_Ioi_sum_reflections
    (fun pq : ℝ × ℝ => ∫ p, F pq.1 pq.2 p ∂ν) hh
  have hsl : ∀ᵐ pq : ℝ × ℝ ∂((volume : Measure ℝ).prod (volume : Measure ℝ)), Integrable (fun p => F pq.1 pq.2 p) ν :=
    hFa.prod_right_ae
  have hmp1 : MeasurePreserving (fun pq : ℝ × ℝ => (-pq.1, pq.2)) ((volume : Measure ℝ).prod (volume : Measure ℝ))
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) :=
    (Measure.measurePreserving_neg (volume : Measure ℝ)).prod (MeasurePreserving.id (volume : Measure ℝ))
  have hmp2 : MeasurePreserving (fun pq : ℝ × ℝ => (pq.1, -pq.2)) ((volume : Measure ℝ).prod (volume : Measure ℝ))
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) :=
    (MeasurePreserving.id (volume : Measure ℝ)).prod (Measure.measurePreserving_neg (volume : Measure ℝ))
  have hsl2 := hmp1.quasiMeasurePreserving.ae hsl
  have hsl3 := hmp2.quasiMeasurePreserving.ae hsl
  have hsl4 := hmp1.quasiMeasurePreserving.ae hsl3
  simp only at hsl2 hsl3 hsl4

  have key' : ∀ᵐ pq : ℝ × ℝ ∂((volume : Measure ℝ).prod (volume : Measure ℝ)), 0 < pq.1 → 0 < pq.2 →
      (∫ p, F pq.1 pq.2 p ∂ν) + (∫ p, F (-pq.1) pq.2 p ∂ν) + (∫ p, F pq.1 (-pq.2) p ∂ν) + (∫ p, F (-pq.1) (-pq.2) p ∂ν) =
      C * ∫ p in Set.Ioi (0 : ℝ), H pq.1 pq.2 p := by
    filter_upwards [hsl, hsl2, hsl3, hsl4] with pq i1 i2 i3 i4 ht hq
    have i12 : Integrable (fun p => F pq.1 pq.2 p + F (-pq.1) pq.2 p) ν := i1.add i2
    have i123 : Integrable (fun p => F pq.1 pq.2 p + F (-pq.1) pq.2 p + F pq.1 (-pq.2) p) ν := i12.add i3
    rw [← integral_add i1 i2, ← integral_add i12 i3, ← integral_add i123 i4, hν, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun p hp => ?_
    have hp : 0 < p := hp
    exact key pq.1 pq.2 p ht hq hp
  have key'' := Measure.ae_ae_of_ae_prod key'
  dsimp only at key'' step2
  rw [step0, step1, step2]
  have step3 : ∫ t in Set.Ioi (0 : ℝ), ∫ q in Set.Ioi (0 : ℝ),
      ((∫ p, F t q p ∂ν) + (∫ p, F (-t) q p ∂ν) + (∫ p, F t (-q) p ∂ν) + (∫ p, F (-t) (-q) p ∂ν)) =
      ∫ t in Set.Ioi (0 : ℝ), ∫ q in Set.Ioi (0 : ℝ), C * ∫ p in Set.Ioi (0 : ℝ), H t q p := by
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi, ae_restrict_of_ae key''] with t ht hk
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi, ae_restrict_of_ae hk] with q hq hk2
    exact hk2 ht hq
  rw [step3]
  simp only [integral_const_mul]

  rcases eq_or_ne C 0 with hC0 | hCst
  · simp [hC0]
  congr 1
  have hswap : ∀ᵐ t : ℝ ∂(volume : Measure ℝ), 0 < t →
      (∫ q in Set.Ioi (0 : ℝ), ∫ p in Set.Ioi (0 : ℝ), H t q p) = ∫ p in Set.Ioi (0 : ℝ), ∫ q in Set.Ioi (0 : ℝ), H t q p := by
    have hst : ∀ᵐ t : ℝ ∂(volume : Measure ℝ), Integrable (fun qp : ℝ × ℝ => F t qp.1 qp.2) ((volume : Measure ℝ).prod ν) :=
      hFint.prod_right_ae
    have hst' : ∀ᵐ t : ℝ ∂(volume : Measure ℝ), Integrable (fun qp : ℝ × ℝ => F (-t) qp.1 qp.2) ((volume : Measure ℝ).prod ν) :=
      (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae hst
    have hmq : MeasurePreserving (fun qp : ℝ × ℝ => (-qp.1, qp.2)) ((volume : Measure ℝ).prod ν) ((volume : Measure ℝ).prod ν) :=
      (Measure.measurePreserving_neg (volume : Measure ℝ)).prod (MeasurePreserving.id ν)
    filter_upwards [hst, hst'] with t i1 i2 ht
    have i3 : Integrable (fun qp : ℝ × ℝ => F t (-qp.1) qp.2) ((volume : Measure ℝ).prod ν) :=
      (hmq.integrable_comp i1.aestronglyMeasurable).mpr i1
    have i4 : Integrable (fun qp : ℝ × ℝ => F (-t) (-qp.1) qp.2) ((volume : Measure ℝ).prod ν) :=
      (hmq.integrable_comp i2.aestronglyMeasurable).mpr i2
    have hsum0 : Integrable (fun qp : ℝ × ℝ => C⁻¹ *
        (F t qp.1 qp.2 + F (-t) qp.1 qp.2 + F t (-qp.1) qp.2 + F (-t) (-qp.1) qp.2))
        ((volume : Measure ℝ).prod ν) := (((i1.add i2).add i3).add i4).const_mul _
    have hmeas_eq : ((volume : Measure ℝ).prod ν) = ((volume : Measure ℝ).prod (volume : Measure ℝ)).restrict (Set.univ ×ˢ Set.Ioi 0) := by
      rw [hν, ← Measure.prod_restrict, Measure.restrict_univ]
    have hsum : Integrable (fun qp : ℝ × ℝ => C⁻¹ *
        (F t qp.1 qp.2 + F (-t) qp.1 qp.2 + F t (-qp.1) qp.2 + F (-t) (-qp.1) qp.2))
        (((volume : Measure ℝ).prod (volume : Measure ℝ)).restrict (Set.Ioi 0 ×ˢ Set.Ioi 0)) := by
      rw [hmeas_eq] at hsum0
      exact hsum0.mono_measure (Measure.restrict_mono (Set.prod_mono (Set.subset_univ _) subset_rfl) le_rfl)
    have hK : Integrable (Function.uncurry fun (q p : ℝ) => H t q p)
        (((volume : Measure ℝ).restrict (Set.Ioi 0)).prod ((volume : Measure ℝ).restrict (Set.Ioi 0))) := by
      rw [Measure.prod_restrict]
      refine hsum.congr ?_
      filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)] with qp hqp
      obtain ⟨hq, hp⟩ := hqp
      have hq : 0 < qp.1 := hq
      have hp : 0 < qp.2 := hp
      have e := key t qp.1 qp.2 ht hq hp
      dsimp only [Function.uncurry]
      rw [e, ← mul_assoc, inv_mul_cancel₀ hCst, one_mul]
    exact integral_integral_swap hK
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi, ae_restrict_of_ae hswap] with t ht hk
  exact hk ht

theorem gamma_close (z₁ z₂ w X : ℂ) (hw : z₁ + z₂ = w) (hz₁ : z₁ ≠ 0) (hz₂ : z₂ ≠ 0) (hw0 : w ≠ 0)
    (hΓw : Complex.Gammaℝ w ≠ 0) :
    Complex.Gammaℝ w *
        (X * (Complex.Gammaℝ z₂ * Complex.Gammaℝ (z₂ + 1) * Complex.Gammaℝ (z₁ + 1) * Complex.Gammaℝ (z₁ + 2)) /
            Complex.Gammaℝ (w + 2) +
          X * (Complex.Gammaℝ (z₂ + 1) * Complex.Gammaℝ (z₂ + 2) * Complex.Gammaℝ z₁ * Complex.Gammaℝ (z₁ + 1)) /
            Complex.Gammaℝ (w + 2)) =
      X * ((Complex.Gammaℝ z₁ * Complex.Gammaℝ (z₁ + 1)) * (Complex.Gammaℝ z₂ * Complex.Gammaℝ (z₂ + 1))) := by
  subst hw
  rw [Complex.Gammaℝ_add_two hz₁, Complex.Gammaℝ_add_two hz₂, Complex.Gammaℝ_add_two hw0]
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
  field_simp

theorem zmod2_cases (c : ZMod 2) : c = 0 ∨ c = 1 := by revert c; decide

theorem dual_pointwise_disc
    (W : ℝ → ℂ) (u : ℂ) (k : ℕ) (hk : 1 ≤ k) {P₂ : RealArchParam} (D : ArchDatumR P₂) (hP₂ : P₂ = RealArchParam.discrete u k hk)
    (ρ : ℂ) (a : ℝ) (ha1 : a = -1) (u₀ cP : ℂ) (a₀ sP : ZMod 2) (hs1 : sP = 1) (n : ℕ) (s : ℂ) (b₀ b₁ b₂ : ℂ)
    (αK βK γK : ℂ) (hαK : αK = s - 3 / 2 - cP - 2 * u) (hβK : βK = u₀ - 2 * u - 2) (hγK : γK = u₀ + cP + 2 * u - 2 * s - 1)
    (t q p : ℝ) (ht : 0 < t) (hq : 0 < q) (hp : 0 < p) (GA GB GD : ℂ)
    (hWA : W t + (-1 : ℂ) ^ a₀.val * W (-t) = (t : ℂ) * GA)
    (hWB : W t + (-1 : ℂ) ^ (a₀ + 1).val * W (-t) = (t : ℂ) * GB)
    (hDW : D.W (ArchR.diagOne (t * p / q)) = ρ * GD)
    (hD0 : D.W (ArchR.diagOne (-(t * p / q))) = 0) :
    (ArchR.quasiChar 0 sP (-t) * ArchR.quasiChar 0 a₀ (-t) * ArchR.quasiChar 0 1 t * ArchR.quasiChar 0 (n : ZMod 2) q * ArchR.quasiChar 0 a₀ q) *
          (W (-t) * (b₀ * (a : ℂ) + b₁ * ((t : ℂ) * (p : ℂ) ^ 2) + b₂ * ((a : ℂ) * (p : ℂ) * ArchR.quasiChar 0 1 t * ((q⁻¹ : ℝ) : ℂ))) * D.W (ArchR.diagOne (a * |t| * p / q))) *
          ((((|t| : ℝ) : ℂ) ^ (s - 5 / 2 - cP - P₂.centralExponent)) * (((|q| : ℝ) : ℂ) ^ (u₀ + cP + P₂.centralExponent - 2 * s - 1)) *
            (((p : ℝ) : ℂ) ^ (u₀ - P₂.centralExponent - 3))) *
          ((Real.exp (-(Real.pi * t ^ 2 * p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / q ^ 2)) : ℂ)) +
    (ArchR.quasiChar 0 sP (-(-t : ℝ)) * ArchR.quasiChar 0 a₀ (-(-t : ℝ)) * ArchR.quasiChar 0 1 (-t : ℝ) * ArchR.quasiChar 0 (n : ZMod 2) q * ArchR.quasiChar 0 a₀ q) *
          (W (-(-t : ℝ)) * (b₀ * (a : ℂ) + b₁ * (((-t : ℝ) : ℂ) * (p : ℂ) ^ 2) + b₂ * ((a : ℂ) * (p : ℂ) * ArchR.quasiChar 0 1 (-t : ℝ) * ((q⁻¹ : ℝ) : ℂ))) * D.W (ArchR.diagOne (a * |(-t : ℝ)| * p / q))) *
          ((((|(-t : ℝ)| : ℝ) : ℂ) ^ (s - 5 / 2 - cP - P₂.centralExponent)) * (((|q| : ℝ) : ℂ) ^ (u₀ + cP + P₂.centralExponent - 2 * s - 1)) *
            (((p : ℝ) : ℂ) ^ (u₀ - P₂.centralExponent - 3))) *
          ((Real.exp (-(Real.pi * (-t : ℝ) ^ 2 * p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / q ^ 2)) : ℂ)) +
    (ArchR.quasiChar 0 sP (-t) * ArchR.quasiChar 0 a₀ (-t) * ArchR.quasiChar 0 1 t * ArchR.quasiChar 0 (n : ZMod 2) (-q : ℝ) * ArchR.quasiChar 0 a₀ (-q : ℝ)) *
          (W (-t) * (b₀ * (a : ℂ) + b₁ * ((t : ℂ) * (p : ℂ) ^ 2) + b₂ * ((a : ℂ) * (p : ℂ) * ArchR.quasiChar 0 1 t * (((-q : ℝ)⁻¹ : ℝ) : ℂ))) * D.W (ArchR.diagOne (a * |t| * p / (-q : ℝ)))) *
          ((((|t| : ℝ) : ℂ) ^ (s - 5 / 2 - cP - P₂.centralExponent)) * (((|(-q : ℝ)| : ℝ) : ℂ) ^ (u₀ + cP + P₂.centralExponent - 2 * s - 1)) *
            (((p : ℝ) : ℂ) ^ (u₀ - P₂.centralExponent - 3))) *
          ((Real.exp (-(Real.pi * t ^ 2 * p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / (-q : ℝ) ^ 2)) : ℂ)) +
    (ArchR.quasiChar 0 sP (-(-t : ℝ)) * ArchR.quasiChar 0 a₀ (-(-t : ℝ)) * ArchR.quasiChar 0 1 (-t : ℝ) * ArchR.quasiChar 0 (n : ZMod 2) (-q : ℝ) * ArchR.quasiChar 0 a₀ (-q : ℝ)) *
          (W (-(-t : ℝ)) * (b₀ * (a : ℂ) + b₁ * (((-t : ℝ) : ℂ) * (p : ℂ) ^ 2) + b₂ * ((a : ℂ) * (p : ℂ) * ArchR.quasiChar 0 1 (-t : ℝ) * (((-q : ℝ)⁻¹ : ℝ) : ℂ))) * D.W (ArchR.diagOne (a * |(-t : ℝ)| * p / (-q : ℝ)))) *
          ((((|(-t : ℝ)| : ℝ) : ℂ) ^ (s - 5 / 2 - cP - P₂.centralExponent)) * (((|(-q : ℝ)| : ℝ) : ℂ) ^ (u₀ + cP + P₂.centralExponent - 2 * s - 1)) *
            (((p : ℝ) : ℂ) ^ (u₀ - P₂.centralExponent - 3))) *
          ((Real.exp (-(Real.pi * (-t : ℝ) ^ 2 * p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / (-q : ℝ) ^ 2)) : ℂ)) =
    ((-1 : ℂ) ^ ((n : ZMod 2)).val * (-1 : ℂ) ^ a₀.val * ρ) *
      (b₀ * (GA * ((t : ℝ) : ℂ) ^ (αK) * GD * ((p : ℝ) : ℂ) ^ (βK - 1) * ((q : ℝ) : ℂ) ^ γK *
          (Real.exp (-(Real.pi / p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * t ^ 2 * p ^ 2)) : ℂ) * (Real.exp (-(Real.pi / q ^ 2)) : ℂ)) +
       b₁ * (GB * ((t : ℝ) : ℂ) ^ (αK + 1) * GD * ((p : ℝ) : ℂ) ^ (βK + 1) * ((q : ℝ) : ℂ) ^ γK *
          (Real.exp (-(Real.pi / p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * t ^ 2 * p ^ 2)) : ℂ) * (Real.exp (-(Real.pi / q ^ 2)) : ℂ)) +
       b₂ * (GB * ((t : ℝ) : ℂ) ^ (αK) * GD * ((p : ℝ) : ℂ) ^ (βK) * ((q : ℝ) : ℂ) ^ (γK - 1) *
          (Real.exp (-(Real.pi / p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * t ^ 2 * p ^ 2)) : ℂ) * (Real.exp (-(Real.pi / q ^ 2)) : ℂ))) := by
  subst ha1 hs1 hP₂ hαK hβK hγK
  have hce : (RealArchParam.discrete u k hk).centralExponent = 2 * u := rfl
  rw [hce]
  have r8 : |t| = t := abs_of_pos ht
  have r9 : |(-t)| = t := by rw [abs_neg, r8]
  have r5 : |q| = q := abs_of_pos hq
  have r7 : |(-q)| = q := by rw [abs_neg, r5]
  rw [r9, r8, r7, r5]
  rw [show (-1 : ℝ) * t * p / q = -(t * p / q) by ring, show (-1 : ℝ) * t * p / -q = t * p / q by ring, hD0, hDW]
  have he1 : ((Real.exp (-(Real.pi * (-1) ^ 2 / p ^ 2)) : ℝ) : ℂ) = ((Real.exp (-(Real.pi / p ^ 2)) : ℝ) : ℂ) := by
    congr 1; congr 1; ring
  have he2 : ((Real.exp (-(Real.pi * (-1) ^ 2 / q ^ 2)) : ℝ) : ℂ) = ((Real.exp (-(Real.pi / q ^ 2)) : ℝ) : ℂ) := by
    congr 1; congr 1; ring

  have mA : ((t : ℝ) : ℂ) ^ (s - 5 / 2 - cP - 2 * u) * ((t : ℝ) : ℂ) * ((p : ℝ) : ℂ) ^ (u₀ - 2 * u - 3) *
      ((q : ℝ) : ℂ) ^ (u₀ + cP + 2 * u - 2 * s - 1) =
      ((t : ℝ) : ℂ) ^ (s - 3 / 2 - cP - 2 * u) * ((p : ℝ) : ℂ) ^ (u₀ - 2 * u - 2 - 1) * ((q : ℝ) : ℂ) ^ (u₀ + cP + 2 * u - 2 * s - 1) := by
    rw [ofReal_cpow_eq_exp ht, ofReal_cpow_eq_exp ht, ofReal_cpow_eq_exp hp, ofReal_cpow_eq_exp hp,
      ofReal_cpow_eq_exp hq, ofReal_eq_exp_log ht]
    simp only [← Complex.exp_add]
    congr 1
    ring
  have mB1 : ((t : ℝ) : ℂ) ^ (s - 5 / 2 - cP - 2 * u) * ((t : ℝ) : ℂ) * ((t : ℝ) : ℂ) *
      (((p : ℝ) : ℂ) ^ (u₀ - 2 * u - 3) * ((p : ℝ) : ℂ) * ((p : ℝ) : ℂ)) * ((q : ℝ) : ℂ) ^ (u₀ + cP + 2 * u - 2 * s - 1) =
      ((t : ℝ) : ℂ) ^ (s - 3 / 2 - cP - 2 * u + 1) * ((p : ℝ) : ℂ) ^ (u₀ - 2 * u - 2 + 1) * ((q : ℝ) : ℂ) ^ (u₀ + cP + 2 * u - 2 * s - 1) := by
    rw [ofReal_cpow_eq_exp ht, ofReal_cpow_eq_exp ht, ofReal_cpow_eq_exp hp, ofReal_cpow_eq_exp hp,
      ofReal_cpow_eq_exp hq, ofReal_eq_exp_log ht, ofReal_eq_exp_log hp]
    simp only [← Complex.exp_add]
    congr 1
    ring
  have mB2 : ((t : ℝ) : ℂ) ^ (s - 5 / 2 - cP - 2 * u) * ((t : ℝ) : ℂ) * (((p : ℝ) : ℂ) ^ (u₀ - 2 * u - 3) * ((p : ℝ) : ℂ)) *
      (((q : ℝ) : ℂ) ^ (u₀ + cP + 2 * u - 2 * s - 1) * ((q : ℝ) : ℂ)⁻¹) =
      ((t : ℝ) : ℂ) ^ (s - 3 / 2 - cP - 2 * u) * ((p : ℝ) : ℂ) ^ (u₀ - 2 * u - 2) * ((q : ℝ) : ℂ) ^ (u₀ + cP + 2 * u - 2 * s - 1 - 1) := by
    rw [ofReal_cpow_eq_exp ht, ofReal_cpow_eq_exp ht, ofReal_cpow_eq_exp hp, ofReal_cpow_eq_exp hp,
      ofReal_cpow_eq_exp hq, ofReal_cpow_eq_exp hq, ofReal_eq_exp_log ht, ofReal_eq_exp_log hp, ofReal_eq_exp_log hq,
      ← Complex.exp_neg]
    simp only [← Complex.exp_add]
    congr 1
    ring
  rcases zmod2_cases a₀ with rfl | rfl
  · rw [show ((0 : ZMod 2) + 1 : ZMod 2) = 1 by decide] at hWB
    simp only [quasiChar_neg _ _ _ ht.ne', quasiChar_neg _ _ _ hq.ne', quasiChar_zero_pos _ ht, quasiChar_zero_pos _ hq,
      v0, v1, pow_zero, pow_one, one_mul, mul_one, neg_one_mul, neg_neg, mul_zero, zero_mul, zero_add] at hWA hWB ⊢
    have hWp : W t = ((t : ℂ) * GA + (t : ℂ) * GB) / 2 := by linear_combination (hWA + hWB) / 2
    have hWm : W (-t) = ((t : ℂ) * GA - (t : ℂ) * GB) / 2 := by linear_combination (hWA - hWB) / 2
    rw [neg_sq t, neg_sq q, he1, he2, inv_neg, hWp, hWm]
    simp only [Complex.ofReal_neg, Complex.ofReal_one, Complex.ofReal_inv]
    linear_combination ((-1 : ℂ) ^ ((n : ZMod 2)).val * ρ * b₀ * GA * GD * (Real.exp (-(Real.pi / p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * t ^ 2 * p ^ 2)) : ℂ) * (Real.exp (-(Real.pi / q ^ 2)) : ℂ)) * mA +
      ((-1 : ℂ) ^ ((n : ZMod 2)).val * ρ * b₁ * GB * GD * (Real.exp (-(Real.pi / p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * t ^ 2 * p ^ 2)) : ℂ) * (Real.exp (-(Real.pi / q ^ 2)) : ℂ)) * mB1 +
      ((-1 : ℂ) ^ ((n : ZMod 2)).val * ρ * b₂ * GB * GD * (Real.exp (-(Real.pi / p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * t ^ 2 * p ^ 2)) : ℂ) * (Real.exp (-(Real.pi / q ^ 2)) : ℂ)) * mB2
  · rw [show ((1 : ZMod 2) + 1 : ZMod 2) = 0 by decide] at hWB
    simp only [quasiChar_neg _ _ _ ht.ne', quasiChar_neg _ _ _ hq.ne', quasiChar_zero_pos _ ht, quasiChar_zero_pos _ hq,
      v0, v1, pow_zero, pow_one, one_mul, mul_one, neg_one_mul, neg_neg, mul_zero, zero_mul, zero_add] at hWA hWB ⊢
    have hWp : W t = ((t : ℂ) * GA + (t : ℂ) * GB) / 2 := by linear_combination (hWA + hWB) / 2
    have hWm : W (-t) = ((t : ℂ) * GB - (t : ℂ) * GA) / 2 := by linear_combination (hWB - hWA) / 2
    rw [neg_sq t, neg_sq q, he1, he2, inv_neg, hWp, hWm]
    simp only [Complex.ofReal_neg, Complex.ofReal_one, Complex.ofReal_inv]
    linear_combination (-((-1 : ℂ) ^ ((n : ZMod 2)).val * ρ * b₀ * GA * GD * (Real.exp (-(Real.pi / p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * t ^ 2 * p ^ 2)) : ℂ) * (Real.exp (-(Real.pi / q ^ 2)) : ℂ))) * mA +
      (-((-1 : ℂ) ^ ((n : ZMod 2)).val * ρ * b₁ * GB * GD * (Real.exp (-(Real.pi / p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * t ^ 2 * p ^ 2)) : ℂ) * (Real.exp (-(Real.pi / q ^ 2)) : ℂ))) * mB1 +
      (-((-1 : ℂ) ^ ((n : ZMod 2)).val * ρ * b₂ * GB * GD * (Real.exp (-(Real.pi / p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * t ^ 2 * p ^ 2)) : ℂ) * (Real.exp (-(Real.pi / q ^ 2)) : ℂ))) * mB2

theorem zmod2_sum_one_of_ne {e₁ e₂ : ZMod 2} (h : e₁ ≠ e₂) : e₁ + e₂ = 1 := by
  revert e₁ e₂; decide

theorem neg_one_pow_val_natCast (k : ℕ) : (-1 : ℂ) ^ ((k : ZMod 2)).val = (-1) ^ k := by
  rw [ZMod.val_natCast, ← neg_one_pow_eq_pow_mod_two]

theorem main_wlog
    (ν₁ ν₂ : ℂ) (a₁ a₂ : ZMod 2) (h12 : a₁ ≠ a₂)
    (W : ℝ → ℂ) (hWc : ContinuousOn W {t : ℝ | t ≠ 0})
    (hW : ∀ b : ZMod 2, ∀ t : ℝ, 0 < t →
      W t + (-1 : ℂ) ^ b.val * W (-t) =
        (t : ℂ) * ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (ν₁ + signShift (a₁ + b)) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t) / r : ℝ) : ℂ) ^ (ν₂ + signShift (a₂ + b)) * (Real.exp (-(Real.pi * ((t) / r) ^ 2)) : ℂ)) / (r : ℂ)))
    (u : ℂ) (k : ℕ) (hk : 1 ≤ k) {P₂ : RealArchParam} (D : ArchDatumR P₂) (hP₂ : P₂ = RealArchParam.discrete u k hk)
    (ρ : ℂ)
    (hρ : (∀ τ : ℝ, 0 < τ →
        D.W (ArchR.diagOne τ) = ρ * ((2 : ℂ) * ((τ : ℂ) ^ (u + (k : ℂ) / 2 + 1) * (Real.exp (-(2 * Real.pi * τ)) : ℂ)))) ∧
      (∀ τ : ℝ, 0 < τ → D.W (ArchR.diagOne (-τ)) = 0))
    (a : ℝ) (ha1 : a = -1) (u₀ cP : ℂ) (hcP : cP = ν₁ + ν₂) (a₀ sP : ZMod 2) (hsP : sP = a₁ + a₂) (n : ℕ) (hn : n = k)
    (ha₀ : a₀ = a₁) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      Complex.Gammaℝ (2 * s - cP - P₂.centralExponent + n + 1) *
        (∫ t : ℝ, ∫ q : ℝ, ∫ p in Set.Ioi (0 : ℝ),
          (ArchR.quasiChar 0 sP (-t) * ArchR.quasiChar 0 a₀ (-t) * ArchR.quasiChar 0 1 t * ArchR.quasiChar 0 (n : ZMod 2) q * ArchR.quasiChar 0 a₀ q) *
          (W (-t) * (-((a : ℂ) + (t : ℂ) * (p : ℂ) ^ 2 + (a : ℂ) * (p : ℂ) * ArchR.quasiChar 0 1 t * ((q⁻¹ : ℝ) : ℂ))) * D.W (ArchR.diagOne (a * |t| * p / q))) *
          ((((|t| : ℝ) : ℂ) ^ (s - 5 / 2 - cP - P₂.centralExponent)) * (((|q| : ℝ) : ℂ) ^ (u₀ + cP + P₂.centralExponent - 2 * s - 1)) *
            (((p : ℝ) : ℂ) ^ (u₀ - P₂.centralExponent - 3))) *
          ((Real.exp (-(Real.pi * t ^ 2 * p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / q ^ 2)) : ℂ))) =
      (-1 : ℂ) ^ (a₀.val + 1 + k) * ρ * (1 / 2 : ℂ) *
        ((Complex.Gammaℝ (s + 1 / 2 + ((-ν₁ + -u₀) + signShift (a₁ + a₀))) *
          Complex.Gammaℝ (s + 1 / 2 + ((-ν₂ + -u₀) + signShift (a₂ + a₀)))) *
          ((Complex.Gammaℝ (s + 1 / 2 + (-ν₁ + (-u + (k : ℂ) / 2))) *
            Complex.Gammaℝ (s + 1 / 2 + (-ν₁ + (-u + (k : ℂ) / 2)) + 1)) *
            (Complex.Gammaℝ (s + 1 / 2 + (-ν₂ + (-u + (k : ℂ) / 2))) *
              Complex.Gammaℝ (s + 1 / 2 + (-ν₂ + (-u + (k : ℂ) / 2)) + 1)))) := by
  have ha : a ≠ 0 := by rw [ha1]; norm_num
  obtain ⟨σI, hI⟩ :=
    LanglandsTunnell.Converse.exists_forall_integrable_dualQuadruple_and_torusTriple_conjBlock_of_mulConvGaussian_sheets
      ν₁ ν₂ a₁ a₂ W hWc hW D a ha u₀ cP a₀ sP n
  subst a₀
  subst n
  have hs1 : sP = 1 := by rw [hsP]; exact zmod2_sum_one_of_ne h12
  have hce : P₂.centralExponent = 2 * u := by rw [hP₂]; rfl
  have e11 : a₁ + a₁ = 0 := CharTwo.add_self_eq_zero a₁
  have e21 : a₂ + a₁ = 1 := by rw [add_comm]; exact zmod2_sum_one_of_ne h12
  have e1s : a₁ + (a₁ + 1) = 1 := by rw [← add_assoc, e11, zero_add]
  have e2s : a₂ + (a₁ + 1) = 0 := by rw [← add_assoc, e21]; decide
  have habs : ∀ x : ℝ, -|x| ≤ x ∧ x ≤ |x| := fun x => ⟨neg_abs_le x, le_abs_self x⟩
  obtain ⟨hu1, hu2⟩ := habs u₀.re
  obtain ⟨hn11, hn12⟩ := habs ν₁.re
  obtain ⟨hn21, hn22⟩ := habs ν₂.re
  obtain ⟨hm1, hm2⟩ := habs u.re
  obtain ⟨hc1, hc2⟩ := habs cP.re
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  set R : ℝ := |u₀.re| + |ν₁.re| + |ν₂.re| + 2 * |u.re| + |cP.re| + 4 with hR
  refine ⟨max σI R, fun s hs => ?_⟩
  have hsI : σI < s.re := lt_of_le_of_lt (le_max_left _ _) hs
  have hsR : R < s.re := lt_of_le_of_lt (le_max_right _ _) hs
  have hR' : |u₀.re| + |ν₁.re| + |ν₂.re| + 2 * |u.re| + |cP.re| + 4 < s.re := by rw [hR] at hsR; exact hsR
  have hcPre : cP.re = ν₁.re + ν₂.re := by rw [hcP, Complex.add_re]

  obtain ⟨Fb, hFb⟩ : ∃ Fb : ℂ → ℂ → ℂ → ℝ → ℝ → ℝ → ℂ, ∀ (b₀ b₁ b₂ : ℂ) (T Q p : ℝ), Fb b₀ b₁ b₂ T Q p =
        (ArchR.quasiChar 0 sP (-T) * ArchR.quasiChar 0 a₁ (-T) * ArchR.quasiChar 0 1 T * ArchR.quasiChar 0 (k : ZMod 2) Q * ArchR.quasiChar 0 a₁ Q) *
          (W (-T) * (b₀ * (a : ℂ) + b₁ * ((T : ℂ) * (p : ℂ) ^ 2) + b₂ * ((a : ℂ) * (p : ℂ) * ArchR.quasiChar 0 1 T * ((Q⁻¹ : ℝ) : ℂ))) * D.W (ArchR.diagOne (a * |T| * p / Q))) *
          ((((|T| : ℝ) : ℂ) ^ (s - 5 / 2 - cP - P₂.centralExponent)) * (((|Q| : ℝ) : ℂ) ^ (u₀ + cP + P₂.centralExponent - 2 * s - 1)) *
            (((p : ℝ) : ℂ) ^ (u₀ - P₂.centralExponent - 3))) *
          ((Real.exp (-(Real.pi * T ^ 2 * p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / Q ^ 2)) : ℂ)) := ⟨_, fun _ _ _ _ _ _ => rfl⟩
  obtain ⟨F, hF⟩ : ∃ F : ℝ → ℝ → ℝ → ℂ, ∀ t q p : ℝ, F t q p =
          (ArchR.quasiChar 0 sP (-t) * ArchR.quasiChar 0 a₁ (-t) * ArchR.quasiChar 0 1 t * ArchR.quasiChar 0 (k : ZMod 2) q * ArchR.quasiChar 0 a₁ q) *
          (W (-t) * (-((a : ℂ) + (t : ℂ) * (p : ℂ) ^ 2 + (a : ℂ) * (p : ℂ) * ArchR.quasiChar 0 1 t * ((q⁻¹ : ℝ) : ℂ))) * D.W (ArchR.diagOne (a * |t| * p / q))) *
          ((((|t| : ℝ) : ℂ) ^ (s - 5 / 2 - cP - P₂.centralExponent)) * (((|q| : ℝ) : ℂ) ^ (u₀ + cP + P₂.centralExponent - 2 * s - 1)) *
            (((p : ℝ) : ℂ) ^ (u₀ - P₂.centralExponent - 3))) *
          ((Real.exp (-(Real.pi * t ^ 2 * p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / q ^ 2)) : ℂ)) := ⟨_, fun _ _ _ => rfl⟩
  simp only [← hF]
  have hFsplit : ∀ t q p : ℝ, F t q p = -(Fb 1 0 0 t q p + Fb 0 1 0 t q p + Fb 0 0 1 t q p) := by
    intro t q p; rw [hF, hFb, hFb, hFb]; ring
  have hFbint : ∀ b₀ b₁ b₂ : ℂ, Integrable (fun x : ℝ × ℝ × ℝ => Fb b₀ b₁ b₂ x.1 x.2.1 x.2.2) ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ioi 0)))) := by
    intro b₀ b₁ b₂
    refine ((hI s hsI).2 b₀ b₁ b₂).congr (ae_of_all _ fun x => ?_)
    simp only [hFb]
  have hsum3 : Integrable (fun x : ℝ × ℝ × ℝ => -(Fb 1 0 0 x.1 x.2.1 x.2.2 + Fb 0 1 0 x.1 x.2.1 x.2.2 + Fb 0 0 1 x.1 x.2.1 x.2.2)) ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ioi 0)))) :=
    (((hFbint 1 0 0).add (hFbint 0 1 0)).add (hFbint 0 0 1)).neg
  have hFint : Integrable (fun x : ℝ × ℝ × ℝ => F x.1 x.2.1 x.2.2) ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ioi 0)))) :=
    hsum3.congr (ae_of_all _ fun x => (hFsplit _ _ _).symm)
  rw [iter_eq_prod F hFint]
  have hlin : ∫ x, F x.1 x.2.1 x.2.2 ∂((volume : Measure ℝ).prod ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ioi 0)))) =
      -((∫ x, Fb 1 0 0 x.1 x.2.1 x.2.2 ∂((volume : Measure ℝ).prod ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ioi 0))))) +
        (∫ x, Fb 0 1 0 x.1 x.2.1 x.2.2 ∂((volume : Measure ℝ).prod ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ioi 0))))) +
        (∫ x, Fb 0 0 1 x.1 x.2.1 x.2.2 ∂((volume : Measure ℝ).prod ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ioi 0)))))) := by
    have i12 : Integrable (fun x : ℝ × ℝ × ℝ => Fb 1 0 0 x.1 x.2.1 x.2.2 + Fb 0 1 0 x.1 x.2.1 x.2.2) ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ioi 0)))) :=
      (hFbint 1 0 0).add (hFbint 0 1 0)
    rw [← integral_add (hFbint 1 0 0) (hFbint 0 1 0), ← integral_add i12 (hFbint 0 0 1), ← integral_neg]
    exact integral_congr_ae (ae_of_all _ fun x => hFsplit _ _ _)
  rw [hlin]

  obtain ⟨αK, hαK⟩ : ∃ x : ℂ, x = s - 3 / 2 - cP - 2 * u := ⟨_, rfl⟩
  obtain ⟨βK, hβK⟩ : ∃ x : ℂ, x = u₀ - 2 * u - 2 := ⟨_, rfl⟩
  obtain ⟨γK, hγK⟩ : ∃ x : ℂ, x = u₀ + cP + 2 * u - 2 * s - 1 := ⟨_, rfl⟩
  obtain ⟨qK, hqK⟩ : ∃ x : ℂ, x = u + (k : ℂ) / 2 + 1 := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ x : ℂ, x = (-1 : ℂ) ^ ((k : ZMod 2)).val * (-1 : ℂ) ^ a₁.val * ρ := ⟨_, rfl⟩

  obtain ⟨HA, hHA⟩ : ∃ H : ℝ → ℝ → ℝ → ℂ, ∀ t q p : ℝ, H t q p =
        ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (ν₁) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t) / r : ℝ) : ℂ) ^ (ν₂ + 1) * (Real.exp (-(Real.pi * ((t) / r) ^ 2)) : ℂ)) / (r : ℂ)) *
          ((t : ℝ) : ℂ) ^ (αK) *
          ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (qK) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t * p / q) / r : ℝ) : ℂ) ^ (qK + 1) * (Real.exp (-(Real.pi * ((t * p / q) / r) ^ 2)) : ℂ)) / (r : ℂ)) *
          ((p : ℝ) : ℂ) ^ (βK - 1) * ((q : ℝ) : ℂ) ^ γK *
          (Real.exp (-(Real.pi / p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * t ^ 2 * p ^ 2)) : ℂ) *
          (Real.exp (-(Real.pi / q ^ 2)) : ℂ) := ⟨_, fun _ _ _ => rfl⟩
  obtain ⟨HB1, hHB1⟩ : ∃ H : ℝ → ℝ → ℝ → ℂ, ∀ t q p : ℝ, H t q p =
        ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (ν₁ + 1) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t) / r : ℝ) : ℂ) ^ (ν₂) * (Real.exp (-(Real.pi * ((t) / r) ^ 2)) : ℂ)) / (r : ℂ)) *
          ((t : ℝ) : ℂ) ^ (αK + 1) *
          ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (qK) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t * p / q) / r : ℝ) : ℂ) ^ (qK + 1) * (Real.exp (-(Real.pi * ((t * p / q) / r) ^ 2)) : ℂ)) / (r : ℂ)) *
          ((p : ℝ) : ℂ) ^ (βK + 1) * ((q : ℝ) : ℂ) ^ γK *
          (Real.exp (-(Real.pi / p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * t ^ 2 * p ^ 2)) : ℂ) *
          (Real.exp (-(Real.pi / q ^ 2)) : ℂ) := ⟨_, fun _ _ _ => rfl⟩
  obtain ⟨HB2, hHB2⟩ : ∃ H : ℝ → ℝ → ℝ → ℂ, ∀ t q p : ℝ, H t q p =
        ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (ν₁ + 1) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              (((t / r : ℝ) : ℂ) ^ ν₂ * (Real.exp (-(Real.pi * (t / r) ^ 2)) : ℂ)) / (r : ℂ)) *
          ((t : ℝ) : ℂ) ^ αK *
          ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ qK * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t * p / q) / r : ℝ) : ℂ) ^ (qK + 1) * (Real.exp (-(Real.pi * ((t * p / q) / r) ^ 2)) : ℂ)) / (r : ℂ)) *
          ((p : ℝ) : ℂ) ^ βK * ((q : ℝ) : ℂ) ^ (γK - 1) *
          (Real.exp (-(Real.pi / p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * t ^ 2 * p ^ 2)) : ℂ) *
          (Real.exp (-(Real.pi / q ^ 2)) : ℂ) := ⟨_, fun _ _ _ => rfl⟩

  have hWA : ∀ t : ℝ, 0 < t → W t + (-1 : ℂ) ^ a₁.val * W (-t) = (t : ℂ) * ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (ν₁) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t) / r : ℝ) : ℂ) ^ (ν₂ + 1) * (Real.exp (-(Real.pi * ((t) / r) ^ 2)) : ℂ)) / (r : ℂ)) := by
    intro t ht
    have h := hW a₁ t ht
    rw [e11, e21, signShift_zero, signShift_one] at h
    simpa only [add_zero] using h
  have hWB : ∀ t : ℝ, 0 < t → W t + (-1 : ℂ) ^ (a₁ + 1).val * W (-t) = (t : ℂ) * ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (ν₁ + 1) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t) / r : ℝ) : ℂ) ^ (ν₂) * (Real.exp (-(Real.pi * ((t) / r) ^ 2)) : ℂ)) / (r : ℂ)) := by
    intro t ht
    have h := hW (a₁ + 1) t ht
    rw [e1s, e2s, signShift_zero, signShift_one] at h
    simpa only [add_zero] using h
  have hDW : ∀ t q p : ℝ, 0 < t → 0 < q → 0 < p → D.W (ArchR.diagOne (t * p / q)) = ρ *
      ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (qK) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t * p / q) / r : ℝ) : ℂ) ^ (qK + 1) * (Real.exp (-(Real.pi * ((t * p / q) / r) ^ 2)) : ℂ)) / (r : ℂ)) := by
    intro t q p ht hq hp
    have hτ : 0 < t * p / q := by positivity
    rw [hρ.1 _ hτ, hqK, discrete_eq _ hτ]
  have hD0 : ∀ t q p : ℝ, 0 < t → 0 < q → 0 < p → D.W (ArchR.diagOne (-(t * p / q))) = 0 := by
    intro t q p ht hq hp
    exact hρ.2 _ (by positivity)
  have keyA : ∀ t q p : ℝ, 0 < t → 0 < q → 0 < p → Fb 1 0 0 t q p + Fb 1 0 0 (-t) q p + Fb 1 0 0 t (-q) p + Fb 1 0 0 (-t) (-q) p = C * HA t q p := by
    intro t q p ht hq hp
    rw [hFb, hFb, hFb, hFb, hHA, hC,
      dual_pointwise_disc W u k hk D hP₂ ρ a ha1 u₀ cP a₁ sP hs1 k s 1 0 0 αK βK γK hαK hβK hγK t q p ht hq hp _ _ _
        (hWA t ht) (hWB t ht) (hDW t q p ht hq hp) (hD0 t q p ht hq hp)]
    ring
  have keyB1 : ∀ t q p : ℝ, 0 < t → 0 < q → 0 < p → Fb 0 1 0 t q p + Fb 0 1 0 (-t) q p + Fb 0 1 0 t (-q) p + Fb 0 1 0 (-t) (-q) p = C * HB1 t q p := by
    intro t q p ht hq hp
    rw [hFb, hFb, hFb, hFb, hHB1, hC,
      dual_pointwise_disc W u k hk D hP₂ ρ a ha1 u₀ cP a₁ sP hs1 k s 0 1 0 αK βK γK hαK hβK hγK t q p ht hq hp _ _ _
        (hWA t ht) (hWB t ht) (hDW t q p ht hq hp) (hD0 t q p ht hq hp)]
    ring
  have keyB2 : ∀ t q p : ℝ, 0 < t → 0 < q → 0 < p → Fb 0 0 1 t q p + Fb 0 0 1 (-t) q p + Fb 0 0 1 t (-q) p + Fb 0 0 1 (-t) (-q) p = C * HB2 t q p := by
    intro t q p ht hq hp
    rw [hFb, hFb, hFb, hFb, hHB2, hC,
      dual_pointwise_disc W u k hk D hP₂ ρ a ha1 u₀ cP a₁ sP hs1 k s 0 0 1 αK βK γK hαK hβK hγK t q p ht hq hp _ _ _
        (hWA t ht) (hWB t ht) (hDW t q p ht hq hp) (hD0 t q p ht hq hp)]
    ring
  rw [fold3 (Fb 1 0 0) HA C (hFbint 1 0 0) keyA, fold3 (Fb 0 1 0) HB1 C (hFbint 0 1 0) keyB1,
    fold3 (Fb 0 0 1) HB2 C (hFbint 0 0 1) keyB2]

  have retac : ∀ z : ℂ, z.re = z.re := fun _ => rfl
  have hbal1 : βK - γK = 2 * αK + 2 + ν₁ + ν₂ := by rw [hαK, hβK, hγK, hcP]; ring
  have hbal2 : βK - (γK - 1) = 2 * αK + 2 + (ν₁ + 1) + ν₂ := by rw [hαK, hβK, hγK, hcP]; ring
  have P1 : 0 < (αK - βK + ν₁ + 1).re := by
    rw [hαK, hβK]; simp only [Complex.add_re, Complex.sub_re, Complex.neg_re, Complex.mul_re, Complex.one_re,
      Complex.re_ofNat, Complex.im_ofNat, Complex.div_ofNat_re, Complex.natCast_re, zero_mul, sub_zero]; linarith
  have P2 : 0 < (αK - βK + ν₂).re := by
    rw [hαK, hβK]; simp only [Complex.add_re, Complex.sub_re, Complex.neg_re, Complex.mul_re, Complex.one_re,
      Complex.re_ofNat, Complex.im_ofNat, Complex.div_ofNat_re, Complex.natCast_re, zero_mul, sub_zero]; linarith
  have P1' : 0 < (αK - βK + (ν₁ + 1)).re := by rw [← add_assoc]; exact P1
  have P3 : 0 < (αK + 1 + ν₁ + qK).re := by
    rw [hαK, hqK]; simp only [Complex.add_re, Complex.sub_re, Complex.neg_re, Complex.mul_re, Complex.one_re,
      Complex.re_ofNat, Complex.im_ofNat, Complex.div_ofNat_re, Complex.natCast_re, zero_mul, sub_zero]; linarith
  have P4 : 0 < (αK + 1 + ν₁ + (qK + 1)).re := by
    have := P3; simp only [Complex.add_re, Complex.one_re] at this ⊢; linarith
  have P5 : 0 < (αK + 2 + ν₂ + qK).re := by
    rw [hαK, hqK]; simp only [Complex.add_re, Complex.sub_re, Complex.neg_re, Complex.mul_re, Complex.one_re,
      Complex.re_ofNat, Complex.im_ofNat, Complex.div_ofNat_re, Complex.natCast_re, zero_mul, sub_zero]; linarith
  have P6 : 0 < (αK + 2 + ν₂ + (qK + 1)).re := by
    have := P5; simp only [Complex.add_re, Complex.one_re] at this ⊢; linarith
  have P7 : 0 < (αK + 1 + (ν₁ + 1) + qK).re := by
    have := P3; simp only [Complex.add_re, Complex.one_re] at this ⊢; linarith
  have P8 : 0 < (αK + 1 + (ν₁ + 1) + (qK + 1)).re := by
    have := P3; simp only [Complex.add_re, Complex.one_re] at this ⊢; linarith
  have P9 : 0 < (αK + 1 + ν₂ + qK).re := by
    rw [hαK, hqK]; simp only [Complex.add_re, Complex.sub_re, Complex.neg_re, Complex.mul_re, Complex.one_re,
      Complex.re_ofNat, Complex.im_ofNat, Complex.div_ofNat_re, Complex.natCast_re, zero_mul, sub_zero]; linarith
  have P10 : 0 < (αK + 1 + ν₂ + (qK + 1)).re := by
    have := P9; simp only [Complex.add_re, Complex.one_re] at this ⊢; linarith
  have hK8pp := LanglandsTunnell.integral_mulConvGaussian_torusGauss_two_term_eq_GammaR_prod_div
    ν₁ ν₂ qK (qK + 1) αK βK γK hbal1 P1 P2 P3 P4 P5 P6
  have hK8p := LanglandsTunnell.integral_mulConvGaussian_torusGauss_eq_GammaR_prod_div_of_balance
    (ν₁ + 1) ν₂ qK (qK + 1) αK βK (γK - 1) hbal2 P1' P2 P7 P8 P9 P10
  have eAB := hK8pp
  simp only [← hHA, ← hHB1] at eAB
  have eB2 := hK8p
  simp only [← hHB2] at eB2
  rw [show ∀ G IA IB1 IB2 : ℂ, G * -(C * IA + C * IB1 + C * IB2) = -(C * (G * ((IA + IB1) + IB2))) from fun _ _ _ _ => by ring,
    eAB, eB2]
  rw [hce, e11, e21, signShift_zero, signShift_one]

  have g1 : Complex.Gammaℝ (αK - βK + ν₁ + 1) = Complex.Gammaℝ (s + 1 / 2 + ((-ν₂ + -u₀) + 1)) := by
    congr 1; rw [hαK, hβK, hcP]; ring
  have g2 : Complex.Gammaℝ (αK - βK + ν₂) = Complex.Gammaℝ (s + 1 / 2 + ((-ν₁ + -u₀) + 0)) := by
    congr 1; rw [hαK, hβK, hcP]; ring
  have g1' : Complex.Gammaℝ (αK - βK + (ν₁ + 1)) = Complex.Gammaℝ (s + 1 / 2 + ((-ν₂ + -u₀) + 1)) := by
    congr 1; rw [hαK, hβK, hcP]; ring
  have g3 : Complex.Gammaℝ (αK + 1 + ν₁ + qK) = Complex.Gammaℝ (s + 1 / 2 + (-ν₂ + (-u + (k : ℂ) / 2))) := by
    congr 1; rw [hαK, hqK, hcP]; ring
  have g4 : Complex.Gammaℝ (αK + 1 + ν₁ + (qK + 1)) = Complex.Gammaℝ (s + 1 / 2 + (-ν₂ + (-u + (k : ℂ) / 2)) + 1) := by
    congr 1; rw [hαK, hqK, hcP]; ring
  have g5 : Complex.Gammaℝ (αK + 2 + ν₂ + qK) = Complex.Gammaℝ (s + 1 / 2 + (-ν₁ + (-u + (k : ℂ) / 2)) + 1) := by
    congr 1; rw [hαK, hqK, hcP]; ring
  have g6 : Complex.Gammaℝ (αK + 2 + ν₂ + (qK + 1)) = Complex.Gammaℝ (s + 1 / 2 + (-ν₁ + (-u + (k : ℂ) / 2)) + 2) := by
    congr 1; rw [hαK, hqK, hcP]; ring
  have g7 : Complex.Gammaℝ (αK + 1 + (ν₁ + 1) + qK) = Complex.Gammaℝ (s + 1 / 2 + (-ν₂ + (-u + (k : ℂ) / 2)) + 1) := by
    congr 1; rw [hαK, hqK, hcP]; ring
  have g8 : Complex.Gammaℝ (αK + 1 + (ν₁ + 1) + (qK + 1)) = Complex.Gammaℝ (s + 1 / 2 + (-ν₂ + (-u + (k : ℂ) / 2)) + 2) := by
    congr 1; rw [hαK, hqK, hcP]; ring
  have g9 : Complex.Gammaℝ (αK + 1 + ν₂ + qK) = Complex.Gammaℝ (s + 1 / 2 + (-ν₁ + (-u + (k : ℂ) / 2))) := by
    congr 1; rw [hαK, hqK, hcP]; ring
  have g10 : Complex.Gammaℝ (αK + 1 + ν₂ + (qK + 1)) = Complex.Gammaℝ (s + 1 / 2 + (-ν₁ + (-u + (k : ℂ) / 2)) + 1) := by
    congr 1; rw [hαK, hqK, hcP]; ring
  have g11 : Complex.Gammaℝ (βK - γK + qK + (qK + 1) + 1) = Complex.Gammaℝ (2 * s - cP - 2 * u + (k : ℂ) + 1 + 2) := by
    congr 1; rw [hβK, hγK, hqK]; ring
  have g12 : Complex.Gammaℝ (βK - (γK - 1) + qK + (qK + 1)) = Complex.Gammaℝ (2 * s - cP - 2 * u + (k : ℂ) + 1 + 2) := by
    congr 1; rw [hβK, hγK, hqK]; ring
  rw [g1, g2, g1', g3, g4, g5, g6, g7, g8, g9, g10, g11, g12]

  have hz₁re : 0 < (s + 1 / 2 + (-ν₁ + (-u + (k : ℂ) / 2))).re := by
    simp only [Complex.add_re, Complex.sub_re, Complex.neg_re, Complex.mul_re, Complex.one_re,
      Complex.re_ofNat, Complex.im_ofNat, Complex.div_ofNat_re, Complex.natCast_re, zero_mul, sub_zero]; linarith
  have hz₂re : 0 < (s + 1 / 2 + (-ν₂ + (-u + (k : ℂ) / 2))).re := by
    simp only [Complex.add_re, Complex.sub_re, Complex.neg_re, Complex.mul_re, Complex.one_re,
      Complex.re_ofNat, Complex.im_ofNat, Complex.div_ofNat_re, Complex.natCast_re, zero_mul, sub_zero]; linarith
  have hwre : 0 < (2 * s - cP - 2 * u + (k : ℂ) + 1).re := by
    simp only [Complex.add_re, Complex.sub_re, Complex.neg_re, Complex.mul_re, Complex.one_re,
      Complex.re_ofNat, Complex.im_ofNat, Complex.div_ofNat_re, Complex.natCast_re, zero_mul, sub_zero]; linarith
  have hne : ∀ z : ℂ, 0 < z.re → z ≠ 0 := fun z hz h => by rw [h, Complex.zero_re] at hz; exact lt_irrefl _ hz
  have hsum : (s + 1 / 2 + (-ν₁ + (-u + (k : ℂ) / 2))) + (s + 1 / 2 + (-ν₂ + (-u + (k : ℂ) / 2))) = 2 * s - cP - 2 * u + (k : ℂ) + 1 := by rw [hcP]; ring
  have hg := gamma_close (s + 1 / 2 + (-ν₁ + (-u + (k : ℂ) / 2))) (s + 1 / 2 + (-ν₂ + (-u + (k : ℂ) / 2))) (2 * s - cP - 2 * u + (k : ℂ) + 1)
    ((1 / 2 : ℂ) * (Complex.Gammaℝ (s + 1 / 2 + ((-ν₂ + -u₀) + 1)) * Complex.Gammaℝ (s + 1 / 2 + ((-ν₁ + -u₀) + 0))))
    hsum (hne _ hz₁re) (hne _ hz₂re) (hne _ hwre) (Complex.Gammaℝ_ne_zero_of_re_pos hwre)
  rw [hC, neg_one_pow_val_natCast]
  linear_combination (-((-1 : ℂ) ^ k * (-1 : ℂ) ^ a₁.val * ρ)) * hg

theorem zmod2_any_of_ne {x y : ZMod 2} (h : x ≠ y) (b : ZMod 2) : b = x ∨ b = y := by
  revert x y b; decide

end P2mKcDualEvalFlatDisc

end

open P2mKcDualEvalFlatDisc in

theorem solution
    (ν₁ ν₂ : ℂ) (a₁ a₂ : ZMod 2) (h12 : a₁ ≠ a₂)
    (W : ℝ → ℂ) (hWc : ContinuousOn W {t : ℝ | t ≠ 0})
    (hW : ∀ b : ZMod 2, ∀ t : ℝ, 0 < t →
      W t + (-1 : ℂ) ^ b.val * W (-t) =
        (t : ℂ) * ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (ν₁ + signShift (a₁ + b)) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t) / r : ℝ) : ℂ) ^ (ν₂ + signShift (a₂ + b)) * (Real.exp (-(Real.pi * ((t) / r) ^ 2)) : ℂ)) / (r : ℂ)))
    (u : ℂ) (k : ℕ) (hk : 1 ≤ k) {P₂ : RealArchParam} (D : ArchDatumR P₂) (hP₂ : P₂ = RealArchParam.discrete u k hk)
    (ρ : ℂ)
    (hρ : (∀ τ : ℝ, 0 < τ →
        D.W (ArchR.diagOne τ) = ρ * ((2 : ℂ) * ((τ : ℂ) ^ (u + (k : ℂ) / 2 + 1) * (Real.exp (-(2 * Real.pi * τ)) : ℂ)))) ∧
      (∀ τ : ℝ, 0 < τ → D.W (ArchR.diagOne (-τ)) = 0))
    (a : ℝ) (ha1 : a = -1) (u₀ cP : ℂ) (hcP : cP = ν₁ + ν₂) (a₀ sP : ZMod 2) (hsP : sP = a₁ + a₂) (n : ℕ) (hn : n = k) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      Complex.Gammaℝ (2 * s - cP - P₂.centralExponent + n + 1) *
        (∫ t : ℝ, ∫ q : ℝ, ∫ p in Set.Ioi (0 : ℝ),
          (ArchR.quasiChar 0 sP (-t) * ArchR.quasiChar 0 a₀ (-t) * ArchR.quasiChar 0 1 t * ArchR.quasiChar 0 (n : ZMod 2) q * ArchR.quasiChar 0 a₀ q) *
          (W (-t) * (-((a : ℂ) + (t : ℂ) * (p : ℂ) ^ 2 + (a : ℂ) * (p : ℂ) * ArchR.quasiChar 0 1 t * ((q⁻¹ : ℝ) : ℂ))) * D.W (ArchR.diagOne (a * |t| * p / q))) *
          ((((|t| : ℝ) : ℂ) ^ (s - 5 / 2 - cP - P₂.centralExponent)) * (((|q| : ℝ) : ℂ) ^ (u₀ + cP + P₂.centralExponent - 2 * s - 1)) *
            (((p : ℝ) : ℂ) ^ (u₀ - P₂.centralExponent - 3))) *
          ((Real.exp (-(Real.pi * t ^ 2 * p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / q ^ 2)) : ℂ))) =
      (-1 : ℂ) ^ (a₀.val + 1 + k) * ρ * (1 / 2 : ℂ) *
        ((Complex.Gammaℝ (s + 1 / 2 + ((-ν₁ + -u₀) + signShift (a₁ + a₀))) *
          Complex.Gammaℝ (s + 1 / 2 + ((-ν₂ + -u₀) + signShift (a₂ + a₀)))) *
          ((Complex.Gammaℝ (s + 1 / 2 + (-ν₁ + (-u + (k : ℂ) / 2))) *
            Complex.Gammaℝ (s + 1 / 2 + (-ν₁ + (-u + (k : ℂ) / 2)) + 1)) *
            (Complex.Gammaℝ (s + 1 / 2 + (-ν₂ + (-u + (k : ℂ) / 2))) *
              Complex.Gammaℝ (s + 1 / 2 + (-ν₂ + (-u + (k : ℂ) / 2)) + 1)))) := by
  rcases zmod2_any_of_ne h12 a₀ with h | h
  · exact main_wlog ν₁ ν₂ a₁ a₂ h12 W hWc hW u k hk D hP₂ ρ hρ a ha1 u₀ cP hcP a₀ sP hsP n hn h
  · have hW' : ∀ b : ZMod 2, ∀ t : ℝ, 0 < t →
        W t + (-1 : ℂ) ^ b.val * W (-t) =
          (t : ℂ) * ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (ν₂ + signShift (a₂ + b)) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t) / r : ℝ) : ℂ) ^ (ν₁ + signShift (a₁ + b)) * (Real.exp (-(Real.pi * ((t) / r) ^ 2)) : ℂ)) / (r : ℂ)) := by
      intro b t ht
      rw [hW b t ht, mulConv_symm _ _ t ht]
    obtain ⟨σ, hσ⟩ := main_wlog ν₂ ν₁ a₂ a₁ h12.symm W hWc hW' u k hk D hP₂ ρ hρ a ha1 u₀ cP
      (hcP.trans (add_comm _ _)) a₀ sP (hsP.trans (add_comm _ _)) n hn h
    exact ⟨σ, fun s hs => (hσ s hs).trans (by ring)⟩

end S_LanglandsTunnell_Converse_GammaR_mul_integral_dualTorusTriple_conjBlock_eq_mul_prod_GammaR_of_discreteProfile
end P2MW
export P2MW.S_LanglandsTunnell_Converse_GammaR_mul_integral_dualTorusTriple_conjBlock_eq_mul_prod_GammaR_of_discreteProfile (solution)
