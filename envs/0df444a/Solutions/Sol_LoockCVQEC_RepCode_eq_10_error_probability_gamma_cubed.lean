-- Prove2me | solution 1 for LoockCVQEC.RepCode.eq_10_error_probability_gamma_cubed
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-09T18:03:49.068185+00:00
-- url     : https://prove2.me/submissions/0a88d815-9b91-4da9-915a-81ca4f88c8d0

import Mathlib
import Definitions.Def_LoockCVQEC_RepCode_Protocol

set_option autoImplicit false

namespace LoockCVQEC.RepCode.Aux

open Real MeasureTheory Filter Topology Matrix

lemma inW_mul_shift (xb pb a x p : ℝ) :
    inW xb pb x p * inW xb pb (x - a) p
      = (4 / π ^ 2 * exp (-a ^ 2) * exp (-4 * (x - (xb + a / 2)) ^ 2)) * exp (-4 * (p - pb) ^ 2) := by
  simp only [inW]
  have e1 : 2 / π * exp (-2 * (x - xb) ^ 2 - 2 * (p - pb) ^ 2) *
      (2 / π * exp (-2 * (x - a - xb) ^ 2 - 2 * (p - pb) ^ 2))
      = 4 / π ^ 2 * exp ((-2 * (x - xb) ^ 2 - 2 * (p - pb) ^ 2) +
          (-2 * (x - a - xb) ^ 2 - 2 * (p - pb) ^ 2)) := by
    rw [Real.exp_add]; ring
  have e2 : 4 / π ^ 2 * exp (-a ^ 2) * exp (-4 * (x - (xb + a / 2)) ^ 2) * exp (-4 * (p - pb) ^ 2)
      = 4 / π ^ 2 * exp (-a ^ 2 + -4 * (x - (xb + a / 2)) ^ 2 + -4 * (p - pb) ^ 2) := by
    rw [Real.exp_add, Real.exp_add]; ring
  rw [e1, e2]
  congr 2
  ring

lemma integrable_inW_mul_shift (xb pb a : ℝ) :
    Integrable (fun v : ℝ × ℝ => inW xb pb v.1 v.2 * inW xb pb (v.1 - a) v.2) := by
  simp_rw [inW_mul_shift]
  rw [Measure.volume_eq_prod]
  have h4 : (0 : ℝ) < 4 := by norm_num
  refine Integrable.mul_prod (f := fun x : ℝ => 4 / π ^ 2 * exp (-a ^ 2) * exp (-4 * (x - (xb + a / 2)) ^ 2))
    (g := fun p : ℝ => exp (-4 * (p - pb) ^ 2)) ?_ ?_
  · exact ((integrable_exp_neg_mul_sq h4).comp_sub_right (xb + a / 2)).const_mul _
  · exact (integrable_exp_neg_mul_sq h4).comp_sub_right pb

lemma inW_overlap (xb pb a : ℝ) :
    π * ∫ v : ℝ × ℝ, inW xb pb v.1 v.2 * inW xb pb (v.1 - a) v.2 = exp (-a ^ 2) := by
  simp_rw [inW_mul_shift]
  rw [Measure.volume_eq_prod, integral_prod_mul
    (f := fun x : ℝ => 4 / π ^ 2 * exp (-a ^ 2) * exp (-4 * (x - (xb + a / 2)) ^ 2))
    (g := fun p : ℝ => exp (-4 * (p - pb) ^ 2))]
  rw [integral_const_mul, integral_sub_right_eq_self (fun x : ℝ => exp (-4 * x ^ 2)),
    integral_sub_right_eq_self (fun x : ℝ => exp (-4 * x ^ 2)), integral_gaussian]
  have hs : √(π / 4) * √(π / 4) = π / 4 := Real.mul_self_sqrt (by positivity)
  have hπ : π ≠ 0 := Real.pi_ne_zero
  calc π * (4 / π ^ 2 * exp (-a ^ 2) * √(π / 4) * √(π / 4))
      = π * (4 / π ^ 2 * exp (-a ^ 2) * (√(π / 4) * √(π / 4))) := by ring
    _ = exp (-a ^ 2) := by rw [hs]; field_simp

lemma fidelity_direct (xb pb γ d : ℝ) :
    fidelity xb pb (directOut γ d (inW xb pb)) = 1 - γ + γ * exp (-d ^ 2) := by
  unfold fidelity directOut
  have h0 := inW_overlap xb pb 0
  have hd := inW_overlap xb pb d
  simp only [sub_zero] at h0
  have e : ∀ v : ℝ × ℝ, inW xb pb v.1 v.2 * ((1 - γ) * inW xb pb v.1 v.2 + γ * inW xb pb (v.1 - d) v.2)
      = (1 - γ) * (inW xb pb v.1 v.2 * inW xb pb v.1 v.2)
        + γ * (inW xb pb v.1 v.2 * inW xb pb (v.1 - d) v.2) := fun v => by ring
  simp_rw [e]
  have i0 := integrable_inW_mul_shift xb pb 0
  simp only [sub_zero] at i0
  rw [integral_add (i0.const_mul _) ((integrable_inW_mul_shift xb pb d).const_mul _),
    integral_const_mul, integral_const_mul]
  norm_num at h0
  calc π * ((1 - γ) * (∫ v : ℝ × ℝ, inW xb pb v.1 v.2 * inW xb pb v.1 v.2)
        + γ * ∫ v : ℝ × ℝ, inW xb pb v.1 v.2 * inW xb pb (v.1 - d) v.2)
      = (1 - γ) * (π * ∫ v : ℝ × ℝ, inW xb pb v.1 v.2 * inW xb pb v.1 v.2)
        + γ * (π * ∫ v : ℝ × ℝ, inW xb pb v.1 v.2 * inW xb pb (v.1 - d) v.2) := by ring
    _ = 1 - γ + γ * exp (-d ^ 2) := by rw [h0, hd]; ring

lemma part3_iff (d γ : ℝ) (hd : 0 < d) (hγ0 : 0 < γ) :
    (1 - γ + γ * exp (-d ^ 2) < 1 - γ ^ 3 + γ ^ 3 * exp (-3 * d ^ 2) ↔
        γ ^ 2 * (1 + exp (-d ^ 2) + exp (-2 * d ^ 2)) < 1) := by
  set a := exp (-d ^ 2) with ha
  have h3 : exp (-3 * d ^ 2) = a ^ 3 := by
    rw [ha, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have h2 : exp (-2 * d ^ 2) = a ^ 2 := by
    rw [ha, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have ha1 : a < 1 := by
    have : 0 < d ^ 2 := by positivity
    rw [ha, ← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  have hpos : 0 < γ * (1 - a) := mul_pos hγ0 (by linarith)
  rw [h3, h2]
  have key : (1 - γ ^ 3 + γ ^ 3 * a ^ 3) - (1 - γ + γ * a)
      = γ * (1 - a) * (1 - γ ^ 2 * (1 + a + a ^ 2)) := by ring
  constructor
  · intro h
    have h' : 0 < γ * (1 - a) * (1 - γ ^ 2 * (1 + a + a ^ 2)) := by linarith
    have := (mul_pos_iff_of_pos_left hpos).mp h'
    linarith
  · intro h
    have := mul_pos hpos (by linarith : 0 < 1 - γ ^ 2 * (1 + a + a ^ 2))
    linarith

lemma sqrt_facts : √(2 / 3) = √2 / √3 ∧ √6 = √2 * √3 ∧ √2 ^ 2 = 2 ∧ √3 ^ 2 = 3 ∧
    0 < √2 ∧ 0 < √3 := by
  refine ⟨Real.sqrt_div (by norm_num) _, ?_, Real.sq_sqrt (by norm_num), Real.sq_sqrt (by norm_num),
    Real.sqrt_pos.2 (by norm_num), Real.sqrt_pos.2 (by norm_num)⟩
  rw [← Real.sqrt_mul (by norm_num)]; norm_num

lemma tritter_mul_transpose : tritter * tritterᵀ = 1 := by
  obtain ⟨e23, e6, s2, s3, p2, p3⟩ := sqrt_facts
  have q2 : √2 ≠ 0 := p2.ne'
  have q3 : √3 ≠ 0 := p3.ne'
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tritter, Matrix.mul_apply, Fin.sum_univ_three, e23, e6] <;>
    field_simp <;> nlinarith [s2, s3]

lemma ancW_split (r a q : ℝ) :
    ancW r a q = 2 / π * exp (-(2 * exp (2 * r)) * a ^ 2) * exp (-(2 * exp (-2 * r)) * q ^ 2) := by
  unfold ancW
  rw [show (2:ℝ) / π * exp (-(2 * exp (2 * r)) * a ^ 2) * exp (-(2 * exp (-2 * r)) * q ^ 2)
      = 2 / π * exp (-(2 * exp (2 * r)) * a ^ 2 + -(2 * exp (-2 * r)) * q ^ 2) by
    rw [Real.exp_add]; ring]
  congr 2; ring

lemma int_ancW (r a : ℝ) :
    ∫ q : ℝ, ancW r a q = 2 / π * exp (-(2 * exp (2 * r)) * a ^ 2) * √(π / (2 * exp (-2 * r))) := by
  simp_rw [ancW_split]; rw [integral_const_mul, integral_gaussian]

lemma kappa_sq (r : ℝ) :
    √(π / (2 * exp (-2 * r))) * √(π / (2 * exp (-2 * r))) = π / (2 * exp (-2 * r)) :=
  Real.mul_self_sqrt (by positivity)

noncomputable def Hk (F : ℝ × ℝ → ℝ) (s : ℝ × ℝ) (r : ℝ) (y : ℝ × ℝ) : ℝ :=
  F y * ((2 / π * exp (-(2 * exp (2 * r)) * (y.1 - s.1) ^ 2) * √(π / (2 * exp (-2 * r)))) *
    (2 / π * exp (-(2 * exp (2 * r)) * (y.2 - s.2) ^ 2) * √(π / (2 * exp (-2 * r)))))

noncomputable def rho2 (u : ℝ × ℝ) : ℝ := 2 / π * (exp (-2 * u.1 ^ 2) * exp (-2 * u.2 ^ 2))

lemma rho2_nonneg (u : ℝ × ℝ) : 0 ≤ rho2 u := by unfold rho2; positivity

lemma rho2_cont : Continuous rho2 := by unfold rho2; fun_prop

lemma rho2_integrable : Integrable rho2 := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  have : Integrable (fun u : ℝ × ℝ => exp (-2 * u.1 ^ 2) * exp (-2 * u.2 ^ 2)) := by
    rw [Measure.volume_eq_prod]
    exact Integrable.mul_prod (integrable_exp_neg_mul_sq h2) (integrable_exp_neg_mul_sq h2)
  exact this.const_mul _

lemma rho2_int : ∫ u, rho2 u = 1 := by
  unfold rho2
  rw [integral_const_mul, Measure.volume_eq_prod,
    integral_prod_mul (f := fun x : ℝ => exp (-2 * x ^ 2)) (g := fun x : ℝ => exp (-2 * x ^ 2)),
    integral_gaussian]
  have hs : √(π / 2) * √(π / 2) = π / 2 := Real.mul_self_sqrt (by positivity)
  rw [hs]; field_simp

lemma rescale (F : ℝ × ℝ → ℝ) (B : ℝ) (s : ℝ × ℝ) (hF : Measurable F) (hB : ∀ y, |F y| ≤ B)
    (r : ℝ) :
    ∫ z : (ℝ × ℝ) × (ℝ × ℝ), F z.1 * ancW r (z.1.1 - s.1) z.2.1 * ancW r (z.1.2 - s.2) z.2.2
      = ∫ u : ℝ × ℝ, F (exp (-r) • u + s) * rho2 u := by
  have hA : (0 : ℝ) < 2 * exp (2 * r) := by positivity
  have hQ : (0 : ℝ) < 2 * exp (-2 * r) := by positivity
  have hint : Integrable (fun z : (ℝ × ℝ) × (ℝ × ℝ) =>
      F z.1 * ancW r (z.1.1 - s.1) z.2.1 * ancW r (z.1.2 - s.2) z.2.2) := by
    have g1 : Integrable (fun y : ℝ × ℝ => exp (-(2 * exp (2 * r)) * (y.1 - s.1) ^ 2) *
        exp (-(2 * exp (2 * r)) * (y.2 - s.2) ^ 2)) := by
      rw [Measure.volume_eq_prod]
      exact Integrable.mul_prod ((integrable_exp_neg_mul_sq hA).comp_sub_right s.1)
        ((integrable_exp_neg_mul_sq hA).comp_sub_right s.2)
    have g2 : Integrable (fun q : ℝ × ℝ => exp (-(2 * exp (-2 * r)) * q.1 ^ 2) *
        exp (-(2 * exp (-2 * r)) * q.2 ^ 2)) := by
      rw [Measure.volume_eq_prod]
      exact Integrable.mul_prod (integrable_exp_neg_mul_sq hQ) (integrable_exp_neg_mul_sq hQ)
    have gg : Integrable (fun z : (ℝ × ℝ) × (ℝ × ℝ) =>
        (exp (-(2 * exp (2 * r)) * (z.1.1 - s.1) ^ 2) * exp (-(2 * exp (2 * r)) * (z.1.2 - s.2) ^ 2)) *
        (exp (-(2 * exp (-2 * r)) * z.2.1 ^ 2) * exp (-(2 * exp (-2 * r)) * z.2.2 ^ 2))) := by
      rw [Measure.volume_eq_prod]; exact g1.mul_prod g2
    refine (gg.const_mul (B * (2 / π) ^ 2)).mono' ?_ ?_
    · exact (by unfold ancW; fun_prop : Measurable (fun z : (ℝ × ℝ) × (ℝ × ℝ) =>
        F z.1 * ancW r (z.1.1 - s.1) z.2.1 * ancW r (z.1.2 - s.2) z.2.2)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun z => ?_
      rw [Real.norm_eq_abs, ancW_split, ancW_split]
      have p1 : 0 ≤ 2 / π * exp (-(2 * exp (2 * r)) * (z.1.1 - s.1) ^ 2) *
          exp (-(2 * exp (-2 * r)) * z.2.1 ^ 2) := by positivity
      have p2 : 0 ≤ 2 / π * exp (-(2 * exp (2 * r)) * (z.1.2 - s.2) ^ 2) *
          exp (-(2 * exp (-2 * r)) * z.2.2 ^ 2) := by positivity
      rw [mul_assoc, abs_mul, abs_of_nonneg (mul_nonneg p1 p2)]
      calc |F z.1| * ((2 / π * exp (-(2 * exp (2 * r)) * (z.1.1 - s.1) ^ 2) *
            exp (-(2 * exp (-2 * r)) * z.2.1 ^ 2)) * (2 / π * exp (-(2 * exp (2 * r)) * (z.1.2 - s.2) ^ 2) *
            exp (-(2 * exp (-2 * r)) * z.2.2 ^ 2)))
          ≤ B * ((2 / π * exp (-(2 * exp (2 * r)) * (z.1.1 - s.1) ^ 2) *
            exp (-(2 * exp (-2 * r)) * z.2.1 ^ 2)) * (2 / π * exp (-(2 * exp (2 * r)) * (z.1.2 - s.2) ^ 2) *
            exp (-(2 * exp (-2 * r)) * z.2.2 ^ 2))) :=
            mul_le_mul_of_nonneg_right (hB _) (mul_nonneg p1 p2)
        _ = _ := by ring
  rw [Measure.volume_eq_prod] at hint
  have E : exp (2 * r) * exp (-r) ^ 2 = 1 := by
    rw [sq, ← Real.exp_add, ← Real.exp_add]; norm_num [show 2 * r + (-r + -r) = 0 by ring]
  have E2 : exp (-2 * r) = exp (-r) ^ 2 := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  have arg : ∀ t : ℝ, -(2 * exp (2 * r)) * (exp (-r) * t) ^ 2 = -2 * t ^ 2 := fun t => by
    linear_combination (-2 * t ^ 2) * E
  have hsc := Measure.integral_comp_smul (μ := (volume : Measure (ℝ × ℝ)))
    (fun w => Hk F s r (w + s)) (exp (-r))
  simp only [Module.finrank_prod, Module.finrank_self, smul_eq_mul] at hsc
  have hpos : 0 < exp (-r) ^ (1 + 1) := by positivity
  rw [abs_of_pos (inv_pos.mpr hpos)] at hsc
  calc (∫ z : (ℝ × ℝ) × (ℝ × ℝ), F z.1 * ancW r (z.1.1 - s.1) z.2.1 * ancW r (z.1.2 - s.2) z.2.2)
      = ∫ y : ℝ × ℝ, ∫ q : ℝ × ℝ, F y * ancW r (y.1 - s.1) q.1 * ancW r (y.2 - s.2) q.2 :=
        integral_prod _ hint
    _ = ∫ y : ℝ × ℝ, Hk F s r y := by
        congr 1; funext y
        simp_rw [mul_assoc]
        rw [integral_const_mul, Measure.volume_eq_prod,
          integral_prod_mul (f := fun q : ℝ => ancW r (y.1 - s.1) q) (g := fun q : ℝ => ancW r (y.2 - s.2) q),
          int_ancW, int_ancW]
        unfold Hk; ring
    _ = ∫ w : ℝ × ℝ, Hk F s r (w + s) := (integral_add_right_eq_self (Hk F s r) s).symm
    _ = ∫ u : ℝ × ℝ, exp (-r) ^ (1 + 1) * Hk F s r (exp (-r) • u + s) := by
        rw [integral_const_mul, hsc]; field_simp
    _ = ∫ u : ℝ × ℝ, F (exp (-r) • u + s) * rho2 u := by
        congr 1; funext u
        unfold Hk rho2
        simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
          add_sub_cancel_right]
        rw [arg, arg]
        have hk := kappa_sq r
        rw [E2] at hk ⊢
        have hπ : π ≠ 0 := Real.pi_ne_zero
        have he : exp (-r) ≠ 0 := (Real.exp_pos _).ne'
        calc exp (-r) ^ (1 + 1) * (F (exp (-r) • u + s) *
              (2 / π * exp (-2 * u.1 ^ 2) * √(π / (2 * exp (-r) ^ 2)) *
                (2 / π * exp (-2 * u.2 ^ 2) * √(π / (2 * exp (-r) ^ 2)))))
            = F (exp (-r) • u + s) * (4 / π ^ 2) * (exp (-r) ^ 2 *
                (√(π / (2 * exp (-r) ^ 2)) * √(π / (2 * exp (-r) ^ 2)))) *
                (exp (-2 * u.1 ^ 2) * exp (-2 * u.2 ^ 2)) := by ring
          _ = _ := by rw [hk]; field_simp; ring

lemma approx_id (F : ℝ × ℝ → ℝ) (B : ℝ) (s : ℝ × ℝ) (hF : Measurable F) (hB : ∀ y, |F y| ≤ B)
    (hc : Tendsto F (𝓝 s) (𝓝 (F s))) :
    Tendsto (fun r : ℝ => ∫ z : (ℝ × ℝ) × (ℝ × ℝ),
      F z.1 * ancW r (z.1.1 - s.1) z.2.1 * ancW r (z.1.2 - s.2) z.2.2) atTop (𝓝 (F s)) := by
  simp_rw [rescale F B s hF hB]
  have key : Tendsto (fun r : ℝ => ∫ u : ℝ × ℝ, F (exp (-r) • u + s) * rho2 u) atTop
      (𝓝 (∫ u : ℝ × ℝ, F s * rho2 u)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun u => B * rho2 u) ?_ ?_ ?_ ?_
    · exact Filter.Eventually.of_forall fun r =>
        (show Measurable (fun u : ℝ × ℝ => F (exp (-r) • u + s) * rho2 u) from
          (hF.comp ((measurable_id.const_smul (exp (-r))).add_const s)).mul
            rho2_cont.measurable).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun r => Filter.Eventually.of_forall fun u => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (rho2_nonneg u)]
      exact mul_le_mul_of_nonneg_right (hB _) (rho2_nonneg u)
    · exact rho2_integrable.const_mul B
    · refine Filter.Eventually.of_forall fun u => ?_
      have h0 : Tendsto (fun r : ℝ => exp (-r)) atTop (𝓝 0) := Real.tendsto_exp_neg_atTop_nhds_zero
      have h1 : Tendsto (fun r : ℝ => exp (-r) • u + s) atTop (𝓝 s) := by
        simpa using (h0.smul_const u).add_const s
      exact (hc.comp h1).mul_const _
  rw [integral_const_mul, rho2_int, mul_one] at key
  exact key

lemma kern_integrable (F : ℝ × ℝ → ℝ) (B : ℝ) (s : ℝ × ℝ) (hF : Measurable F) (hB : ∀ y, |F y| ≤ B)
    (r : ℝ) : Integrable (fun z : (ℝ × ℝ) × (ℝ × ℝ) =>
      F z.1 * ancW r (z.1.1 - s.1) z.2.1 * ancW r (z.1.2 - s.2) z.2.2) := by
  have hA : (0 : ℝ) < 2 * exp (2 * r) := by positivity
  have hQ : (0 : ℝ) < 2 * exp (-2 * r) := by positivity
  have g1 : Integrable (fun y : ℝ × ℝ => exp (-(2 * exp (2 * r)) * (y.1 - s.1) ^ 2) *
      exp (-(2 * exp (2 * r)) * (y.2 - s.2) ^ 2)) := by
    rw [Measure.volume_eq_prod]
    exact Integrable.mul_prod ((integrable_exp_neg_mul_sq hA).comp_sub_right s.1)
      ((integrable_exp_neg_mul_sq hA).comp_sub_right s.2)
  have g2 : Integrable (fun q : ℝ × ℝ => exp (-(2 * exp (-2 * r)) * q.1 ^ 2) *
      exp (-(2 * exp (-2 * r)) * q.2 ^ 2)) := by
    rw [Measure.volume_eq_prod]
    exact Integrable.mul_prod (integrable_exp_neg_mul_sq hQ) (integrable_exp_neg_mul_sq hQ)
  have gg : Integrable (fun z : (ℝ × ℝ) × (ℝ × ℝ) =>
      (exp (-(2 * exp (2 * r)) * (z.1.1 - s.1) ^ 2) * exp (-(2 * exp (2 * r)) * (z.1.2 - s.2) ^ 2)) *
      (exp (-(2 * exp (-2 * r)) * z.2.1 ^ 2) * exp (-(2 * exp (-2 * r)) * z.2.2 ^ 2))) := by
    rw [Measure.volume_eq_prod]; exact g1.mul_prod g2
  refine (gg.const_mul (B * (2 / π) ^ 2)).mono' ?_ ?_
  · exact (by unfold ancW; fun_prop : Measurable (fun z : (ℝ × ℝ) × (ℝ × ℝ) =>
      F z.1 * ancW r (z.1.1 - s.1) z.2.1 * ancW r (z.1.2 - s.2) z.2.2)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun z => ?_
    rw [Real.norm_eq_abs, ancW_split, ancW_split]
    have p1 : 0 ≤ 2 / π * exp (-(2 * exp (2 * r)) * (z.1.1 - s.1) ^ 2) *
        exp (-(2 * exp (-2 * r)) * z.2.1 ^ 2) := by positivity
    have p2 : 0 ≤ 2 / π * exp (-(2 * exp (2 * r)) * (z.1.2 - s.2) ^ 2) *
        exp (-(2 * exp (-2 * r)) * z.2.2 ^ 2) := by positivity
    rw [mul_assoc, abs_mul, abs_of_nonneg (mul_nonneg p1 p2)]
    calc |F z.1| * ((2 / π * exp (-(2 * exp (2 * r)) * (z.1.1 - s.1) ^ 2) *
          exp (-(2 * exp (-2 * r)) * z.2.1 ^ 2)) * (2 / π * exp (-(2 * exp (2 * r)) * (z.1.2 - s.2) ^ 2) *
          exp (-(2 * exp (-2 * r)) * z.2.2 ^ 2)))
        ≤ B * ((2 / π * exp (-(2 * exp (2 * r)) * (z.1.1 - s.1) ^ 2) *
          exp (-(2 * exp (-2 * r)) * z.2.1 ^ 2)) * (2 / π * exp (-(2 * exp (2 * r)) * (z.1.2 - s.2) ^ 2) *
          exp (-(2 * exp (-2 * r)) * z.2.2 ^ 2))) :=
          mul_le_mul_of_nonneg_right (hB _) (mul_nonneg p1 p2)
      _ = _ := by ring

lemma kern_bound (F : ℝ × ℝ → ℝ) (B : ℝ) (s : ℝ × ℝ) (hF : Measurable F) (hB : ∀ y, |F y| ≤ B)
    (r : ℝ) : |∫ z : (ℝ × ℝ) × (ℝ × ℝ),
      F z.1 * ancW r (z.1.1 - s.1) z.2.1 * ancW r (z.1.2 - s.2) z.2.2| ≤ B := by
  rw [rescale F B s hF hB r]
  have h := norm_integral_le_of_norm_le (rho2_integrable.const_mul B)
    (Filter.Eventually.of_forall fun u => (by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (rho2_nonneg u)]
      exact mul_le_mul_of_nonneg_right (hB _) (rho2_nonneg u) :
        ‖F (exp (-r) • u + s) * rho2 u‖ ≤ B * rho2 u))
  rwa [integral_const_mul, rho2_int, mul_one, Real.norm_eq_abs] at h

lemma pf_e (y2 y3 : ℝ) : paperFeedforward ∅ y2 y3 = 0 := by
  unfold paperFeedforward
  rw [if_neg (show (∅ : Finset (Fin 3)) ≠ {0} by decide), if_neg (show (∅ : Finset (Fin 3)) ≠ {1} by decide), if_neg (show (∅ : Finset (Fin 3)) ≠ {2} by decide), if_neg (show (∅ : Finset (Fin 3)) ≠ {0, 1} by decide), if_neg (show (∅ : Finset (Fin 3)) ≠ {0, 2} by decide), if_neg (show (∅ : Finset (Fin 3)) ≠ {1, 2} by decide)]

lemma pf_0 (y2 y3 : ℝ) : paperFeedforward {0} y2 y3 = y2 / √2 := by
  unfold paperFeedforward
  rw [if_pos rfl]

lemma pf_1 (y2 y3 : ℝ) : paperFeedforward {1} y2 y3 = √(2 / 3) * y3 := by
  unfold paperFeedforward
  rw [if_neg (show ({1} : Finset (Fin 3)) ≠ {0} by decide), if_pos rfl]

lemma pf_2 (y2 y3 : ℝ) : paperFeedforward {2} y2 y3 = -(√(2 / 3) * y3) := by
  unfold paperFeedforward
  rw [if_neg (show ({2} : Finset (Fin 3)) ≠ {0} by decide), if_neg (show ({2} : Finset (Fin 3)) ≠ {1} by decide), if_pos rfl]

lemma pf_01 (y2 y3 : ℝ) : paperFeedforward {0, 1} y2 y3 = 2 * √(2 / 3) * y3 := by
  unfold paperFeedforward
  rw [if_neg (show ({0, 1} : Finset (Fin 3)) ≠ {0} by decide), if_neg (show ({0, 1} : Finset (Fin 3)) ≠ {1} by decide), if_neg (show ({0, 1} : Finset (Fin 3)) ≠ {2} by decide), if_pos rfl]

lemma pf_02 (y2 y3 : ℝ) : paperFeedforward {0, 2} y2 y3 = -(2 * √(2 / 3) * y3) := by
  unfold paperFeedforward
  rw [if_neg (show ({0, 2} : Finset (Fin 3)) ≠ {0} by decide), if_neg (show ({0, 2} : Finset (Fin 3)) ≠ {1} by decide), if_neg (show ({0, 2} : Finset (Fin 3)) ≠ {2} by decide), if_neg (show ({0, 2} : Finset (Fin 3)) ≠ {0, 1} by decide), if_pos rfl]

lemma pf_12 (y2 y3 : ℝ) : paperFeedforward {1, 2} y2 y3 = -(√2 * y2) := by
  unfold paperFeedforward
  rw [if_neg (show ({1, 2} : Finset (Fin 3)) ≠ {0} by decide), if_neg (show ({1, 2} : Finset (Fin 3)) ≠ {1} by decide), if_neg (show ({1, 2} : Finset (Fin 3)) ≠ {2} by decide), if_neg (show ({1, 2} : Finset (Fin 3)) ≠ {0, 1} by decide), if_neg (show ({1, 2} : Finset (Fin 3)) ≠ {0, 2} by decide), if_pos rfl]

lemma val_e (d : ℝ) : paperFeedforward ∅ (syndrome d ∅).1 (syndrome d ∅).2 = (tritter *ᵥ errVec d ∅) 0 := by
  rw [pf_e]
  simp [errVec, mulVec, dotProduct, Fin.sum_univ_three]

lemma val_0 (d : ℝ) :
    paperFeedforward {0} (syndrome d {0}).1 (syndrome d {0}).2 = (tritter *ᵥ errVec d {0}) 0 := by
  obtain ⟨e23, e6, s2, s3, p2, p3⟩ := sqrt_facts
  have q2 : √2 ≠ 0 := p2.ne'
  have q3 : √3 ≠ 0 := p3.ne'
  rw [pf_0]
  simp [syndrome, errVec, mulVec, dotProduct, Fin.sum_univ_three, tritter, e23, e6]
  all_goals (try field_simp)
  all_goals ring

lemma val_1 (d : ℝ) :
    paperFeedforward {1} (syndrome d {1}).1 (syndrome d {1}).2 = (tritter *ᵥ errVec d {1}) 0 := by
  obtain ⟨e23, e6, s2, s3, p2, p3⟩ := sqrt_facts
  have q2 : √2 ≠ 0 := p2.ne'
  have q3 : √3 ≠ 0 := p3.ne'
  rw [pf_1]
  simp [syndrome, errVec, mulVec, dotProduct, Fin.sum_univ_three, tritter, e23, e6]
  all_goals (try field_simp)
  all_goals ring

lemma val_2 (d : ℝ) :
    paperFeedforward {2} (syndrome d {2}).1 (syndrome d {2}).2 = (tritter *ᵥ errVec d {2}) 0 := by
  obtain ⟨e23, e6, s2, s3, p2, p3⟩ := sqrt_facts
  have q2 : √2 ≠ 0 := p2.ne'
  have q3 : √3 ≠ 0 := p3.ne'
  rw [pf_2]
  simp [syndrome, errVec, mulVec, dotProduct, Fin.sum_univ_three, tritter, e23, e6]
  all_goals (try field_simp)
  all_goals ring

lemma val_01 (d : ℝ) :
    paperFeedforward {0, 1} (syndrome d {0, 1}).1 (syndrome d {0, 1}).2 = (tritter *ᵥ errVec d {0, 1}) 0 := by
  obtain ⟨e23, e6, s2, s3, p2, p3⟩ := sqrt_facts
  have q2 : √2 ≠ 0 := p2.ne'
  have q3 : √3 ≠ 0 := p3.ne'
  rw [pf_01]
  simp [syndrome, errVec, mulVec, dotProduct, Fin.sum_univ_three, tritter, e23, e6]
  all_goals (try field_simp)
  all_goals ring

lemma val_02 (d : ℝ) :
    paperFeedforward {0, 2} (syndrome d {0, 2}).1 (syndrome d {0, 2}).2 = (tritter *ᵥ errVec d {0, 2}) 0 := by
  obtain ⟨e23, e6, s2, s3, p2, p3⟩ := sqrt_facts
  have q2 : √2 ≠ 0 := p2.ne'
  have q3 : √3 ≠ 0 := p3.ne'
  rw [pf_02]
  simp [syndrome, errVec, mulVec, dotProduct, Fin.sum_univ_three, tritter, e23, e6]
  all_goals (try field_simp)
  all_goals ring

lemma val_12 (d : ℝ) :
    paperFeedforward {1, 2} (syndrome d {1, 2}).1 (syndrome d {1, 2}).2 = (tritter *ᵥ errVec d {1, 2}) 0 := by
  obtain ⟨e23, e6, s2, s3, p2, p3⟩ := sqrt_facts
  have q2 : √2 ≠ 0 := p2.ne'
  have q3 : √3 ≠ 0 := p3.ne'
  rw [pf_12]
  simp [syndrome, errVec, mulVec, dotProduct, Fin.sum_univ_three, tritter, e23, e6]
  all_goals (try field_simp)
  all_goals ring

lemma univ_facts (d : ℝ) : (tritter *ᵥ errVec d Finset.univ) 0 = √3 * d ∧
    (tritter *ᵥ errVec d Finset.univ) 1 = 0 ∧ (tritter *ᵥ errVec d Finset.univ) 2 = 0 ∧
    syndrome d ∅ = (0, 0) := by
  obtain ⟨e23, e6, s2, s3, p2, p3⟩ := sqrt_facts
  have q3 : √3 ≠ 0 := p3.ne'
  have hs3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  have h236 : √(2 / 3) = 2 / √6 := by
    rw [show (2 : ℝ) / 3 = 4 / 6 by norm_num, Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 4) 6,
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  have h3 : (√3)⁻¹ = √3 / 3 := by field_simp <;> nlinarith [hs3, s3]
  have h3' : 1 / √3 = √3 / 3 := by rw [one_div, h3]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [errVec, mulVec, dotProduct, Fin.sum_univ_three, tritter, h3, h3'] <;> ring
  · simp [errVec, mulVec, dotProduct, Fin.sum_univ_three, tritter, h236] <;> ring
  · simp [errVec, mulVec, dotProduct, Fin.sum_univ_three, tritter]
  · simp [syndrome, errVec, mulVec, dotProduct, Fin.sum_univ_three]

lemma center (d : ℝ) (hd : 0 < d) (S : Finset (Fin 3)) :
    ((syndrome d S).1 - (syndrome d S).1) ^ 2 + ((syndrome d S).2 - (syndrome d S).2) ^ 2 < d ^ 2 / 6 := by
  simp only [sub_self]; nlinarith [pow_pos hd 2]

lemma cont_ff (d : ℝ) (hd : 0 < d) (φ : ℝ → ℝ → ℝ) (hff : ∀ S : Finset (Fin 3), S ≠ Finset.univ → ∀ y2 y3 : ℝ,
      (y2 - (syndrome d S).1) ^ 2 + (y3 - (syndrome d S).2) ^ 2 < d ^ 2 / 6 →
        φ y2 y3 = paperFeedforward S y2 y3)
    (S : Finset (Fin 3)) (hS : S ≠ Finset.univ) :
    Tendsto (fun y : ℝ × ℝ => φ y.1 y.2) (𝓝 (syndrome d S)) (𝓝 (φ (syndrome d S).1 (syndrome d S).2)) := by
  rw [hff S hS _ _ (center d hd S)]
  have hcont : Continuous (fun y : ℝ × ℝ => paperFeedforward S y.1 y.2) := by
    unfold paperFeedforward; split_ifs <;> fun_prop
  refine (hcont.tendsto (syndrome d S)).congr' ?_
  have hopen : IsOpen {y : ℝ × ℝ | (y.1 - (syndrome d S).1) ^ 2 + (y.2 - (syndrome d S).2) ^ 2 < d ^ 2 / 6} :=
    isOpen_lt (by fun_prop) (by fun_prop)
  filter_upwards [hopen.mem_nhds (center d hd S)] with y hy
  exact (hff S hS y.1 y.2 hy).symm

noncomputable def Fv (xb pb x1 p1 : ℝ) (φ : ℝ → ℝ → ℝ) (v : Fin 3 → ℝ) (y : ℝ × ℝ) : ℝ :=
  inW xb pb (x1 + φ y.1 y.2 - v 0) p1

noncomputable def Iv (xb pb r x1 p1 : ℝ) (φ : ℝ → ℝ → ℝ) (v : Fin 3 → ℝ) : ℝ :=
  ∫ z : (ℝ × ℝ) × (ℝ × ℝ), Fv xb pb x1 p1 φ v z.1 * ancW r (z.1.1 - v 1) z.2.1 * ancW r (z.1.2 - v 2) z.2.2

lemma inW_nonneg (xb pb x p : ℝ) : 0 ≤ inW xb pb x p := by unfold inW; positivity

lemma inW_abs_le (xb pb x p : ℝ) : |inW xb pb x p| ≤ 2 / π := by
  rw [abs_of_nonneg (inW_nonneg xb pb x p)]
  unfold inW
  have h1 : exp (-2 * (x - xb) ^ 2 - 2 * (p - pb) ^ 2) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by nlinarith [sq_nonneg (x - xb), sq_nonneg (p - pb)])
  have hπ : (0 : ℝ) ≤ 2 / π := by positivity
  calc 2 / π * exp (-2 * (x - xb) ^ 2 - 2 * (p - pb) ^ 2) ≤ 2 / π * 1 :=
        mul_le_mul_of_nonneg_left h1 hπ
    _ = 2 / π := mul_one _

lemma Fv_meas (xb pb x1 p1 : ℝ) (φ : ℝ → ℝ → ℝ) (v : Fin 3 → ℝ)
    (hφ : Measurable (Function.uncurry φ)) : Measurable (Fv xb pb x1 p1 φ v) := by
  have h2 : Measurable (fun y : ℝ × ℝ => φ y.1 y.2) := hφ
  show Measurable (fun y : ℝ × ℝ => inW xb pb (x1 + φ y.1 y.2 - v 0) p1)
  unfold inW
  fun_prop

lemma Fv_bound (xb pb x1 p1 : ℝ) (φ : ℝ → ℝ → ℝ) (v : Fin 3 → ℝ) :
    ∀ y, |Fv xb pb x1 p1 φ v y| ≤ 2 / π := fun _ => inW_abs_le _ _ _ _

lemma lim_v (xb pb x1 p1 : ℝ) (φ : ℝ → ℝ → ℝ) (v : Fin 3 → ℝ) (hφ : Measurable (Function.uncurry φ))
    (hc : Tendsto (fun y : ℝ × ℝ => φ y.1 y.2) (𝓝 (v 1, v 2)) (𝓝 (φ (v 1) (v 2)))) :
    Tendsto (fun r : ℝ => Iv xb pb r x1 p1 φ v) atTop
      (𝓝 (inW xb pb (x1 + φ (v 1) (v 2) - v 0) p1)) := by
  have hcont : Continuous (fun x : ℝ => inW xb pb x p1) := by unfold inW; fun_prop
  have hF := (hcont.tendsto _).comp ((hc.const_add x1).sub_const (v 0))
  exact approx_id (Fv xb pb x1 p1 φ v) (2 / π) (v 1, v 2) (Fv_meas xb pb x1 p1 φ v hφ)
    (Fv_bound xb pb x1 p1 φ v) hF

lemma lim_S (xb pb d x1 p1 : ℝ) (hd : 0 < d) (φ : ℝ → ℝ → ℝ) (hφ : Measurable (Function.uncurry φ))
    (hff : ∀ S : Finset (Fin 3), S ≠ Finset.univ → ∀ y2 y3 : ℝ,
      (y2 - (syndrome d S).1) ^ 2 + (y3 - (syndrome d S).2) ^ 2 < d ^ 2 / 6 →
        φ y2 y3 = paperFeedforward S y2 y3)
    (S : Finset (Fin 3)) (hS : S ≠ Finset.univ)
    (hval : paperFeedforward S (syndrome d S).1 (syndrome d S).2 = (tritter *ᵥ errVec d S) 0) :
    Tendsto (fun r : ℝ => Iv xb pb r x1 p1 φ (tritter *ᵥ errVec d S)) atTop (𝓝 (inW xb pb x1 p1)) := by
  have h := lim_v xb pb x1 p1 φ (tritter *ᵥ errVec d S) hφ (cont_ff d hd φ hff S hS)
  have e : φ ((tritter *ᵥ errVec d S) 1) ((tritter *ᵥ errVec d S) 2) = (tritter *ᵥ errVec d S) 0 := by
    rw [← hval]; exact hff S hS _ _ (center d hd S)
  rw [e, add_sub_cancel_right] at h
  exact h

lemma lim_univ (xb pb d x1 p1 : ℝ) (hd : 0 < d) (φ : ℝ → ℝ → ℝ) (hφ : Measurable (Function.uncurry φ))
    (hff : ∀ S : Finset (Fin 3), S ≠ Finset.univ → ∀ y2 y3 : ℝ,
      (y2 - (syndrome d S).1) ^ 2 + (y3 - (syndrome d S).2) ^ 2 < d ^ 2 / 6 →
        φ y2 y3 = paperFeedforward S y2 y3) :
    Tendsto (fun r : ℝ => Iv xb pb r x1 p1 φ (tritter *ᵥ errVec d Finset.univ)) atTop
      (𝓝 (inW xb pb (x1 - √3 * d) p1)) := by
  have hne : (∅ : Finset (Fin 3)) ≠ Finset.univ := by decide
  obtain ⟨h0, h1, h2, hE⟩ := univ_facts d
  have hc : Tendsto (fun y : ℝ × ℝ => φ y.1 y.2)
      (𝓝 ((tritter *ᵥ errVec d Finset.univ) 1, (tritter *ᵥ errVec d Finset.univ) 2))
      (𝓝 (φ ((tritter *ᵥ errVec d Finset.univ) 1) ((tritter *ᵥ errVec d Finset.univ) 2))) := by
    have := cont_ff d hd φ hff ∅ hne
    rw [hE] at this
    rw [h1, h2]
    exact this
  have h := lim_v xb pb x1 p1 φ _ hφ hc
  have e : φ 0 0 = 0 := by
    have := hff ∅ hne _ _ (center d hd ∅)
    rw [hE, pf_e] at this
    exact this
  rw [h1, h2, e, h0, add_zero] at h
  exact h

lemma C1 (x u : Fin 3 → ℝ) : tritter *ᵥ (tritterᵀ *ᵥ x - u) = x - tritter *ᵥ u := by
  rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, tritter_mul_transpose, Matrix.one_mulVec]

lemma C1' (x : Fin 3 → ℝ) : tritter *ᵥ (tritterᵀ *ᵥ x) = x := by
  rw [Matrix.mulVec_mulVec, tritter_mul_transpose, Matrix.one_mulVec]

lemma ev_e (d : ℝ) : errVec d ∅ = 0 := by
  funext i; fin_cases i <;> simp [errVec, Pi.single_apply]

lemma ev_0 (d : ℝ) : errVec d {0} = Pi.single 0 d := by
  funext i; fin_cases i <;> simp [errVec, Pi.single_apply]

lemma ev_1 (d : ℝ) : errVec d {1} = Pi.single 1 d := by
  funext i; fin_cases i <;> simp [errVec, Pi.single_apply]

lemma ev_2 (d : ℝ) : errVec d {2} = Pi.single 2 d := by
  funext i; fin_cases i <;> simp [errVec, Pi.single_apply]

lemma ev_01 (d : ℝ) : errVec d {0, 1} = Pi.single 0 d + Pi.single 1 d := by
  funext i; fin_cases i <;> simp [errVec, Pi.single_apply]

lemma ev_02 (d : ℝ) : errVec d {0, 2} = Pi.single 0 d + Pi.single 2 d := by
  funext i; fin_cases i <;> simp [errVec, Pi.single_apply]

lemma ev_12 (d : ℝ) : errVec d {1, 2} = Pi.single 1 d + Pi.single 2 d := by
  funext i; fin_cases i <;> simp [errVec, Pi.single_apply]

lemma ev_u (d : ℝ) : errVec d Finset.univ = Pi.single 0 d + Pi.single 1 d + Pi.single 2 d := by
  funext i; fin_cases i <;> simp [errVec, Pi.single_apply]

def Ss : Fin 8 → Finset (Fin 3) := ![∅, {2}, {1}, {1, 2}, {0}, {0, 2}, {0, 1}, Finset.univ]

noncomputable def wts (a b : ℝ) : Fin 8 → ℝ :=
  ![a ^ 3, a ^ 2 * b, a ^ 2 * b, a * b ^ 2, a ^ 2 * b, a * b ^ 2, a * b ^ 2, b ^ 3]

noncomputable def Lv (A B : ℝ) : Fin 8 → ℝ := ![A, A, A, A, A, A, A, B]

lemma decoded_eq (xb pb r γ d : ℝ) (x p : Fin 3 → ℝ) :
    decoded xb pb r γ d x p = ∑ i, wts (1 - γ) γ i * prodW xb pb r (x - tritter *ᵥ errVec d (Ss i)) p := by
  rw [Fin.sum_univ_eight]
  show _ = (1 - γ) ^ 3 * prodW xb pb r (x - tritter *ᵥ errVec d ∅) p
    + (1 - γ) ^ 2 * γ * prodW xb pb r (x - tritter *ᵥ errVec d {2}) p
    + (1 - γ) ^ 2 * γ * prodW xb pb r (x - tritter *ᵥ errVec d {1}) p
    + (1 - γ) * γ ^ 2 * prodW xb pb r (x - tritter *ᵥ errVec d {1, 2}) p
    + (1 - γ) ^ 2 * γ * prodW xb pb r (x - tritter *ᵥ errVec d {0}) p
    + (1 - γ) * γ ^ 2 * prodW xb pb r (x - tritter *ᵥ errVec d {0, 2}) p
    + (1 - γ) * γ ^ 2 * prodW xb pb r (x - tritter *ᵥ errVec d {0, 1}) p
    + γ ^ 3 * prodW xb pb r (x - tritter *ᵥ errVec d Finset.univ) p
  rw [ev_e, ev_2, ev_1, ev_12, ev_0, ev_02, ev_01, ev_u]
  simp only [decoded, decode, noisy, errMode, encode, sub_sub, C1, C1', Matrix.mulVec_zero, sub_zero]
  ring

lemma prodW_vec (xb pb r a b c p q1 q2 : ℝ) (v : Fin 3 → ℝ) :
    prodW xb pb r (![a, b, c] - v) ![p, q1, q2]
      = inW xb pb (a - v 0) p * ancW r (b - v 1) q1 * ancW r (c - v 2) q2 := by
  simp [prodW]

lemma output_eq (xb pb r γ d : ℝ) (φ : ℝ → ℝ → ℝ) (hφ : Measurable (Function.uncurry φ)) (x1 p1 : ℝ) :
    output xb pb r γ d φ x1 p1
      = ∑ i, wts (1 - γ) γ i * Iv xb pb r x1 p1 φ (tritter *ᵥ errVec d (Ss i)) := by
  unfold output
  simp_rw [decoded_eq, prodW_vec]
  rw [integral_finset_sum]
  · simp_rw [integral_const_mul]; rfl
  · intro i _
    exact (kern_integrable (Fv xb pb x1 p1 φ (tritter *ᵥ errVec d (Ss i))) (2 / π)
      ((tritter *ᵥ errVec d (Ss i)) 1, (tritter *ᵥ errVec d (Ss i)) 2)
      (Fv_meas xb pb x1 p1 φ _ hφ) (Fv_bound xb pb x1 p1 φ _) r).const_mul _

lemma wts_nonneg (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : ∀ i, 0 ≤ wts a b i := by
  intro i
  fin_cases i
  exacts [pow_nonneg ha 3, mul_nonneg (pow_nonneg ha 2) hb, mul_nonneg (pow_nonneg ha 2) hb,
    mul_nonneg ha (pow_nonneg hb 2), mul_nonneg (pow_nonneg ha 2) hb, mul_nonneg ha (pow_nonneg hb 2),
    mul_nonneg ha (pow_nonneg hb 2), pow_nonneg hb 3]

lemma wts_sum (γ : ℝ) : ∑ i, wts (1 - γ) γ i = 1 := by
  rw [Fin.sum_univ_eight]
  show (1 - γ) ^ 3 + (1 - γ) ^ 2 * γ + (1 - γ) ^ 2 * γ + (1 - γ) * γ ^ 2 + (1 - γ) ^ 2 * γ
    + (1 - γ) * γ ^ 2 + (1 - γ) * γ ^ 2 + γ ^ 3 = 1
  ring

lemma hsum (γ A B : ℝ) : ∑ i, wts (1 - γ) γ i * Lv A B i = (1 - γ ^ 3) * A + γ ^ 3 * B := by
  rw [Fin.sum_univ_eight]
  show (1 - γ) ^ 3 * A + (1 - γ) ^ 2 * γ * A + (1 - γ) ^ 2 * γ * A + (1 - γ) * γ ^ 2 * A
    + (1 - γ) ^ 2 * γ * A + (1 - γ) * γ ^ 2 * A + (1 - γ) * γ ^ 2 * A + γ ^ 3 * B = _
  ring

lemma output_abs_le (xb pb r γ d : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (φ : ℝ → ℝ → ℝ)
    (hφ : Measurable (Function.uncurry φ)) (x1 p1 : ℝ) :
    |output xb pb r γ d φ x1 p1| ≤ 2 / π := by
  rw [output_eq xb pb r γ d φ hφ x1 p1]
  have hw := wts_nonneg (1 - γ) γ (by linarith) hγ0.le
  calc |∑ i, wts (1 - γ) γ i * Iv xb pb r x1 p1 φ (tritter *ᵥ errVec d (Ss i))|
      ≤ ∑ i, |wts (1 - γ) γ i * Iv xb pb r x1 p1 φ (tritter *ᵥ errVec d (Ss i))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, wts (1 - γ) γ i * (2 / π) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [abs_mul, abs_of_nonneg (hw i)]
        exact mul_le_mul_of_nonneg_left (kern_bound (Fv xb pb x1 p1 φ (tritter *ᵥ errVec d (Ss i))) (2 / π)
          ((tritter *ᵥ errVec d (Ss i)) 1, (tritter *ᵥ errVec d (Ss i)) 2)
          (Fv_meas xb pb x1 p1 φ _ hφ) (Fv_bound xb pb x1 p1 φ _) r) (hw i)
    _ = 2 / π := by rw [← Finset.sum_mul, wts_sum]; ring

lemma output_meas (xb pb r γ d : ℝ) (φ : ℝ → ℝ → ℝ) (hφ : Measurable (Function.uncurry φ)) :
    Measurable (fun v : ℝ × ℝ => output xb pb r γ d φ v.1 v.2) := by
  have hφw : Measurable (fun w : (ℝ × ℝ) × ((ℝ × ℝ) × (ℝ × ℝ)) => φ w.2.1.1 w.2.1.2) :=
    hφ.comp (by fun_prop : Measurable (fun w : (ℝ × ℝ) × ((ℝ × ℝ) × (ℝ × ℝ)) => (w.2.1.1, w.2.1.2)))
  have hf : Measurable (fun w : (ℝ × ℝ) × ((ℝ × ℝ) × (ℝ × ℝ)) =>
      decoded xb pb r γ d ![w.1.1 + φ w.2.1.1 w.2.1.2, w.2.1.1, w.2.1.2] ![w.1.2, w.2.2.1, w.2.2.2]) := by
    simp_rw [decoded_eq, prodW_vec]
    apply Finset.measurable_sum
    intro i _
    unfold inW ancW
    fun_prop
  have h2 : StronglyMeasurable (fun v : ℝ × ℝ => ∫ z : (ℝ × ℝ) × (ℝ × ℝ),
      decoded xb pb r γ d ![v.1 + φ z.1.1 z.1.2, z.1.1, z.1.2] ![v.2, z.2.1, z.2.2]) :=
    hf.stronglyMeasurable.integral_prod_right'
  exact h2.measurable

lemma integrable_inW (xb pb : ℝ) : Integrable (fun v : ℝ × ℝ => inW xb pb v.1 v.2) := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  have e : (fun v : ℝ × ℝ => inW xb pb v.1 v.2)
      = fun v : ℝ × ℝ => (2 / π * exp (-2 * (v.1 - xb) ^ 2)) * exp (-2 * (v.2 - pb) ^ 2) := by
    funext v; unfold inW
    rw [show -2 * (v.1 - xb) ^ 2 - 2 * (v.2 - pb) ^ 2 = -2 * (v.1 - xb) ^ 2 + -2 * (v.2 - pb) ^ 2 by ring,
      Real.exp_add]; ring
  rw [e, Measure.volume_eq_prod]
  exact Integrable.mul_prod (f := fun x : ℝ => 2 / π * exp (-2 * (x - xb) ^ 2))
    (g := fun p : ℝ => exp (-2 * (p - pb) ^ 2))
    (((integrable_exp_neg_mul_sq h2).comp_sub_right xb).const_mul _)
    ((integrable_exp_neg_mul_sq h2).comp_sub_right pb)

lemma part1 (xb pb d γ : ℝ) (hd : 0 < d) (φ : ℝ → ℝ → ℝ) (hφ : Measurable (Function.uncurry φ))
    (hff : ∀ S : Finset (Fin 3), S ≠ Finset.univ → ∀ y2 y3 : ℝ,
      (y2 - (syndrome d S).1) ^ 2 + (y3 - (syndrome d S).2) ^ 2 < d ^ 2 / 6 →
        φ y2 y3 = paperFeedforward S y2 y3) (x1 p1 : ℝ) :
    Tendsto (fun r : ℝ => output xb pb r γ d φ x1 p1) atTop
      (𝓝 ((1 - γ ^ 3) * inW xb pb x1 p1 + γ ^ 3 * inW xb pb (x1 - √3 * d) p1)) := by
  have hlim : ∀ i : Fin 8, Tendsto (fun r : ℝ => Iv xb pb r x1 p1 φ (tritter *ᵥ errVec d (Ss i))) atTop
      (𝓝 (Lv (inW xb pb x1 p1) (inW xb pb (x1 - √3 * d) p1) i)) := by
    intro i
    fin_cases i
    exacts [lim_S xb pb d x1 p1 hd φ hφ hff ∅ (by decide) (val_e d),
      lim_S xb pb d x1 p1 hd φ hφ hff {2} (by decide) (val_2 d),
      lim_S xb pb d x1 p1 hd φ hφ hff {1} (by decide) (val_1 d),
      lim_S xb pb d x1 p1 hd φ hφ hff {1, 2} (by decide) (val_12 d),
      lim_S xb pb d x1 p1 hd φ hφ hff {0} (by decide) (val_0 d),
      lim_S xb pb d x1 p1 hd φ hφ hff {0, 2} (by decide) (val_02 d),
      lim_S xb pb d x1 p1 hd φ hφ hff {0, 1} (by decide) (val_01 d),
      lim_univ xb pb d x1 p1 hd φ hφ hff]
  have key := tendsto_finset_sum (Finset.univ : Finset (Fin 8))
    (fun i _ => (hlim i).const_mul (wts (1 - γ) γ i))
  rw [hsum] at key
  exact key.congr fun r => (output_eq xb pb r γ d φ hφ x1 p1).symm

lemma part2 (xb pb d γ : ℝ) (hd : 0 < d) (hγ0 : 0 < γ) (hγ1 : γ < 1) (φ : ℝ → ℝ → ℝ)
    (hφ : Measurable (Function.uncurry φ)) (hff : ∀ S : Finset (Fin 3), S ≠ Finset.univ → ∀ y2 y3 : ℝ,
      (y2 - (syndrome d S).1) ^ 2 + (y3 - (syndrome d S).2) ^ 2 < d ^ 2 / 6 →
        φ y2 y3 = paperFeedforward S y2 y3) :
    Tendsto (fun r : ℝ => fidelity xb pb (output xb pb r γ d φ)) atTop
      (𝓝 (1 - γ ^ 3 + γ ^ 3 * exp (-3 * d ^ 2))) := by
  have hconv : Tendsto (fun r : ℝ => ∫ v : ℝ × ℝ, inW xb pb v.1 v.2 * output xb pb r γ d φ v.1 v.2) atTop
      (𝓝 (∫ v : ℝ × ℝ, inW xb pb v.1 v.2 * directOut (γ ^ 3) (√3 * d) (inW xb pb) v.1 v.2)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun v => inW xb pb v.1 v.2 * (2 / π))
      ?_ ?_ ?_ ?_
    · exact Filter.Eventually.of_forall fun r =>
        ((by unfold inW; fun_prop : Measurable (fun v : ℝ × ℝ => inW xb pb v.1 v.2)).mul
          (output_meas xb pb r γ d φ hφ)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun r => Filter.Eventually.of_forall fun v => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (inW_nonneg _ _ _ _)]
      exact mul_le_mul_of_nonneg_left (output_abs_le xb pb r γ d hγ0 hγ1 φ hφ v.1 v.2) (inW_nonneg _ _ _ _)
    · exact (integrable_inW xb pb).mul_const _
    · exact Filter.Eventually.of_forall fun v =>
        (part1 xb pb d γ hd φ hφ hff v.1 v.2).const_mul (inW xb pb v.1 v.2)
  have h := hconv.const_mul π
  have hfd := fidelity_direct xb pb (γ ^ 3) (√3 * d)
  unfold fidelity at hfd
  rw [hfd] at h
  have e : -(√3 * d) ^ 2 = -3 * d ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]; ring
  rw [e] at h
  exact h

end LoockCVQEC.RepCode.Aux

open LoockCVQEC.RepCode Real MeasureTheory Filter Topology in
theorem solution (xb pb d γ : ℝ) (hd : 0 < d)
    (hγ0 : 0 < γ) (hγ1 : γ < 1) (φ : ℝ → ℝ → ℝ) (hφ : Measurable (Function.uncurry φ))
    (hff : ∀ S : Finset (Fin 3), S ≠ Finset.univ → ∀ y2 y3 : ℝ,
      (y2 - (syndrome d S).1) ^ 2 + (y3 - (syndrome d S).2) ^ 2 < d ^ 2 / 6 →
        φ y2 y3 = paperFeedforward S y2 y3) :
    (∀ x1 p1 : ℝ, Tendsto (fun r : ℝ => output xb pb r γ d φ x1 p1) atTop
        (𝓝 ((1 - γ ^ 3) * inW xb pb x1 p1 + γ ^ 3 * inW xb pb (x1 - √3 * d) p1)))
    ∧ Tendsto (fun r : ℝ => fidelity xb pb (output xb pb r γ d φ)) atTop
        (𝓝 (1 - γ ^ 3 + γ ^ 3 * exp (-3 * d ^ 2)))
    ∧ (fidelity xb pb (directOut γ d (inW xb pb)) < 1 - γ ^ 3 + γ ^ 3 * exp (-3 * d ^ 2) ↔
        γ ^ 2 * (1 + exp (-d ^ 2) + exp (-2 * d ^ 2)) < 1) := by
  refine ⟨fun x1 p1 => Aux.part1 xb pb d γ hd φ hφ hff x1 p1,
    Aux.part2 xb pb d γ hd hγ0 hγ1 φ hφ hff, ?_⟩
  rw [Aux.fidelity_direct]
  exact Aux.part3_iff d γ hd hγ0
