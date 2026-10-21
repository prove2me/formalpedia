-- Prove2me | solution 1 for MassartDKW.Tight.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T02:49:53.148782+00:00
-- url     : https://prove2.me/submissions/24ef7ea5-df48-4e93-86e6-25b61e9ec85e

import Mathlib
import Definitions.Def_MassartDKW_Tight_Analytic

set_option autoImplicit false

open MeasureTheory Real MassartDKW.Tight

namespace CsLib

noncomputable def ff (y : ℝ) : ℝ := (1 - y / √(1 + y ^ 2)) / 2

lemma r_pos (y : ℝ) : 0 < √(1 + y ^ 2) := Real.sqrt_pos.2 (by positivity)

lemma r_sq (y : ℝ) : √(1 + y ^ 2) ^ 2 = 1 + y ^ 2 := Real.sq_sqrt (by positivity)

lemma ff_hasDeriv (y : ℝ) : HasDerivAt ff (-(1 / 2) / √(1 + y ^ 2) ^ 3) y := by
  have h1 : HasDerivAt (fun y : ℝ => √(1 + y ^ 2)) (y / √(1 + y ^ 2)) y := by
    have := ((hasDerivAt_pow 2 y).const_add 1).sqrt (by positivity)
    convert this using 1
    have := r_pos y
    field_simp
    norm_num
    ring
  have h2 := (hasDerivAt_id' y).div h1 (r_pos y).ne'
  have h3 := ((hasDerivAt_const y (1 : ℝ)).sub h2).div_const 2
  have hr := r_pos y
  have hs := r_sq y
  have hval : (0 - (1 * √(1 + y ^ 2) - y * (y / √(1 + y ^ 2))) / √(1 + y ^ 2) ^ 2) / 2 =
      -(1 / 2) / √(1 + y ^ 2) ^ 3 := by
    field_simp
    nlinarith [hs]
  exact HasDerivAt.congr_deriv (f := ff) h3 hval

lemma ff_anti : StrictAnti ff := by
  apply strictAnti_of_deriv_neg
  intro y
  rw [(ff_hasDeriv y).deriv]
  have := r_pos y
  have : 0 < √(1 + y ^ 2) ^ 3 := by positivity
  have : -(1 / 2 : ℝ) / √(1 + y ^ 2) ^ 3 < 0 := div_neg_of_neg_of_pos (by norm_num) this
  exact this

lemma ff_image : ff '' Set.univ = Set.Ioo 0 1 := by
  ext u
  constructor
  · rintro ⟨y, -, rfl⟩
    have hr := r_pos y
    have hs := r_sq y
    have h1 : y / √(1 + y ^ 2) < 1 := by
      rw [div_lt_one hr]
      nlinarith [hs, sq_nonneg (√(1 + y ^ 2) - y)]
    have h2 : -1 < y / √(1 + y ^ 2) := by
      rw [lt_div_iff₀ hr]
      nlinarith [hs, sq_nonneg (√(1 + y ^ 2) + y)]
    unfold ff
    constructor <;> linarith
  · rintro ⟨h0, h1⟩
    have hq : 0 < u * (1 - u) := mul_pos h0 (by linarith)
    set q := u * (1 - u) with hqdef
    have hsq := Real.sqrt_pos.2 hq
    have hsq2 := Real.sq_sqrt hq.le
    refine ⟨(1 - 2 * u) / (2 * √q), Set.mem_univ _, ?_⟩
    have hr : √(1 + ((1 - 2 * u) / (2 * √q)) ^ 2) = 1 / (2 * √q) := by
      rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)]
      field_simp
      nlinarith [hsq2, hqdef]
    unfold ff
    rw [hr]
    field_simp
    ring

lemma master (g : ℝ → ℝ) :
    ∫ u in (0 : ℝ)..1, g u = ∫ y : ℝ, ((1 / 2) / √(1 + y ^ 2) ^ 3) * g (ff y) := by
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo, ← ff_image]
  rw [integral_image_eq_integral_abs_deriv_smul (f := ff) (f' := fun y => -(1 / 2) / √(1 + y ^ 2) ^ 3)
    MeasurableSet.univ (fun x _ => (ff_hasDeriv x).hasDerivWithinAt) ff_anti.injective.injOn g]
  rw [Measure.restrict_univ]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  have hr := r_pos y
  have : |-(1 / 2 : ℝ) / √(1 + y ^ 2) ^ 3| = (1 / 2) / √(1 + y ^ 2) ^ 3 := by
    rw [abs_of_neg (div_neg_of_neg_of_pos (by norm_num) (by positivity))]
    ring
  simp only [smul_eq_mul, this]

lemma gauss2 (b : ℝ) (hb : 0 < b) :
    ∫ y : ℝ, y ^ 2 * Real.exp (-b * y ^ 2) = √(π / b) / (2 * b) := by
  have h := integral_comp_abs (f := fun x : ℝ => x ^ 2 * Real.exp (-b * x ^ 2))
  simp only [sq_abs] at h
  rw [h]
  have h2 := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := 2) (b := b) (by norm_num) (by norm_num) hb
  simp only [Real.rpow_two] at h2
  rw [h2]
  have hG : Real.Gamma ((2 + 1) / 2) = √π / 2 := by
    have : ((2 : ℝ) + 1) / 2 = 1 / 2 + 1 := by norm_num
    rw [this, Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]
    ring
  rw [hG]
  have hb' : b ^ (-(2 + 1) / 2 : ℝ) = (b * √b)⁻¹ := by
    have : (-(2 + 1) / 2 : ℝ) = -1 + (-(1 / 2)) := by norm_num
    rw [this, Real.rpow_add hb, Real.rpow_neg_one, Real.rpow_neg hb.le, ← Real.sqrt_eq_rpow]
    simp [mul_comm]
  rw [hb', Real.sqrt_div Real.pi_pos.le]
  have := Real.sqrt_pos.2 hb
  field_simp

lemma rp (A : ℝ) (hA : 0 < A) (a : ℕ) :
    A ^ (-(1 / 2 : ℝ) - (a : ℝ)) = (√A)⁻¹ * (A ^ a)⁻¹ := by
  rw [Real.rpow_sub hA, Real.rpow_neg hA.le, ← Real.sqrt_eq_rpow, Real.rpow_natCast, div_eq_mul_inv]

lemma ff_facts (y : ℝ) :
    0 < ff y ∧ 0 < 1 - ff y ∧ ff y * (1 - ff y) = 1 / (4 * (1 + y ^ 2)) ∧
      (ff y)⁻¹ = 2 * (1 + y ^ 2) * (1 + y / √(1 + y ^ 2)) ∧
      (1 - ff y)⁻¹ = 2 * (1 + y ^ 2) * (1 - y / √(1 + y ^ 2)) := by
  have hr := r_pos y
  have hs := r_sq y
  have hmem : ff y ∈ Set.Ioo (0 : ℝ) 1 := by rw [← ff_image]; exact ⟨y, Set.mem_univ _, rfl⟩
  obtain ⟨h0, h1⟩ := hmem
  have hA : ff y = (√(1 + y ^ 2) - y) / (2 * √(1 + y ^ 2)) := by unfold ff; field_simp
  have hB : 1 - ff y = (√(1 + y ^ 2) + y) / (2 * √(1 + y ^ 2)) := by rw [hA]; field_simp; ring
  have hp : (√(1 + y ^ 2) - y) * (√(1 + y ^ 2) + y) = 1 := by nlinarith [hs]
  have hne1 : √(1 + y ^ 2) - y ≠ 0 := by
    intro h; rw [h] at hp; simp at hp
  have hne2 : √(1 + y ^ 2) + y ≠ 0 := by
    intro h; rw [h] at hp; simp at hp
  refine ⟨h0, by linarith, ?_, ?_, ?_⟩
  · rw [hB, hA]; field_simp; nlinarith [hs]
  · rw [hA]; field_simp; nlinarith [hs]
  · rw [hB]; field_simp; nlinarith [hs]

lemma pt (a b : ℕ) (y : ℝ) :
    (1 / 2) / √(1 + y ^ 2) ^ 3 * ((ff y) ^ (-(1 / 2 : ℝ) - (a : ℝ)) * (1 - ff y) ^ (-(1 / 2 : ℝ) - (b : ℝ))) =
      (1 / (1 + y ^ 2)) * (2 * (1 + y ^ 2) * (1 + y / √(1 + y ^ 2))) ^ a *
        (2 * (1 + y ^ 2) * (1 - y / √(1 + y ^ 2))) ^ b := by
  obtain ⟨hA, hB, hAB, hAi, hBi⟩ := ff_facts y
  have hr := r_pos y
  have hs := r_sq y
  rw [rp _ hA, rp _ hB, ← inv_pow, ← inv_pow, hAi, hBi]
  have hsq : √(ff y) * √(1 - ff y) = 1 / (2 * √(1 + y ^ 2)) := by
    rw [← Real.sqrt_mul hA.le, hAB, Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)]
    field_simp
    nlinarith [hs]
  have hsa : 0 < √(ff y) := Real.sqrt_pos.2 hA
  have hsb : 0 < √(1 - ff y) := Real.sqrt_pos.2 hB
  have : (√(ff y))⁻¹ * (√(1 - ff y))⁻¹ = 2 * √(1 + y ^ 2) := by
    rw [← mul_inv, hsq]; field_simp
  calc _ = (1 / 2) / √(1 + y ^ 2) ^ 3 * ((√(ff y))⁻¹ * (√(1 - ff y))⁻¹) *
        ((2 * (1 + y ^ 2) * (1 + y / √(1 + y ^ 2))) ^ a * (2 * (1 + y ^ 2) * (1 - y / √(1 + y ^ 2))) ^ b) := by ring
    _ = _ := by
      rw [this]
      have h3 : (1 / 2) / √(1 + y ^ 2) ^ 3 * (2 * √(1 + y ^ 2)) = 1 / (1 + y ^ 2) := by
        field_simp
        nlinarith [hs]
      rw [h3]
      ring

lemma Kgen (l : ℝ) (a b : ℕ) :
    ∫ u in (0 : ℝ)..1, u ^ (-(1 / 2 : ℝ) - (a : ℝ)) * (1 - u) ^ (-(1 / 2 : ℝ) - (b : ℝ)) *
        Real.exp (-(l ^ 2) / (2 * u * (1 - u))) =
      ∫ y : ℝ, (1 / (1 + y ^ 2)) * (2 * (1 + y ^ 2) * (1 + y / √(1 + y ^ 2))) ^ a *
        (2 * (1 + y ^ 2) * (1 - y / √(1 + y ^ 2))) ^ b * Real.exp (-(2 * l ^ 2) * (1 + y ^ 2)) := by
  rw [master]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  obtain ⟨hA, hB, hAB, -, -⟩ := ff_facts y
  have hex : -(l ^ 2) / (2 * ff y * (1 - ff y)) = -(2 * l ^ 2) * (1 + y ^ 2) := by
    have : 2 * ff y * (1 - ff y) = 1 / (2 * (1 + y ^ 2)) := by
      rw [mul_assoc, hAB]; field_simp; try ring
    rw [this]; field_simp
  simp only [hex]
  have := pt a b y
  calc _ = ((1 / 2) / √(1 + y ^ 2) ^ 3 * ((ff y) ^ (-(1 / 2 : ℝ) - (a : ℝ)) *
        (1 - ff y) ^ (-(1 / 2 : ℝ) - (b : ℝ)))) * Real.exp (-(2 * l ^ 2) * (1 + y ^ 2)) := by ring
    _ = _ := by rw [this]

lemma F_conv (a b : ℕ) (y : ℝ) :
    (1 / (1 + y ^ 2)) * (2 * (1 + y ^ 2) * (1 + y / √(1 + y ^ 2))) ^ a *
        (2 * (1 + y ^ 2) * (1 - y / √(1 + y ^ 2))) ^ b =
      (1 - (y / √(1 + y ^ 2)) ^ 2) * (2 * √(1 + y ^ 2) ^ 2 * (1 + y / √(1 + y ^ 2))) ^ a *
        (2 * √(1 + y ^ 2) ^ 2 * (1 - y / √(1 + y ^ 2))) ^ b := by
  have hr := r_pos y
  have hs := r_sq y
  have h1 : 1 / (1 + y ^ 2) = 1 - (y / √(1 + y ^ 2)) ^ 2 := by
    rw [div_pow, hs]; field_simp; ring
  rw [h1, hs]

lemma rel (y : ℝ) : √(1 + y ^ 2) ^ 2 * (1 - (y / √(1 + y ^ 2)) ^ 2) = 1 := by
  have hr := r_pos y
  have hs := r_sq y
  rw [div_pow, hs]; field_simp; ring

lemma A10 (r t : ℝ) (h : r ^ 2 * (1 - t ^ 2) = 1) :
    (1 - t ^ 2) * (2 * r ^ 2 * (1 + t)) ^ 1 * (2 * r ^ 2 * (1 - t)) ^ 0 = 2 + 2 * t := by
  linear_combination (2 * (1 + t)) * h

lemma A11 (r t : ℝ) (h : r ^ 2 * (1 - t ^ 2) = 1) :
    (1 - t ^ 2) * (2 * r ^ 2 * (1 + t)) ^ 1 * (2 * r ^ 2 * (1 - t)) ^ 1 = 4 := by
  linear_combination (4 * (r ^ 2 * (1 - t ^ 2) + 1)) * h

lemma A20 (r t : ℝ) (h : r ^ 2 * (1 - t ^ 2) = 1) :
    (1 - t ^ 2) * (2 * r ^ 2 * (1 + t)) ^ 2 * (2 * r ^ 2 * (1 - t)) ^ 0 =
      4 * r ^ 2 * (1 + t ^ 2) + 8 * r ^ 2 * t := by
  linear_combination (4 * r ^ 2 * (1 + t) ^ 2) * h

lemma A21 (r t : ℝ) (h : r ^ 2 * (1 - t ^ 2) = 1) :
    (1 - t ^ 2) * (2 * r ^ 2 * (1 + t)) ^ 2 * (2 * r ^ 2 * (1 - t)) ^ 1 =
      8 * r ^ 2 + 8 * r ^ 2 * t := by
  linear_combination (8 * r ^ 2 * (1 + t) * (r ^ 2 * (1 - t ^ 2) + 1)) * h

lemma A22 (r t : ℝ) (h : r ^ 2 * (1 - t ^ 2) = 1) :
    (1 - t ^ 2) * (2 * r ^ 2 * (1 + t)) ^ 2 * (2 * r ^ 2 * (1 - t)) ^ 2 = 16 * r ^ 2 := by
  linear_combination (16 * r ^ 2 * ((r ^ 2 * (1 - t ^ 2)) ^ 2 + r ^ 2 * (1 - t ^ 2) + 1)) * h

lemma Efac (b y : ℝ) : Real.exp (-b * (1 + y ^ 2)) = Real.exp (-b) * Real.exp (-b * y ^ 2) := by
  rw [← Real.exp_add]; ring_nf

lemma hE (b : ℝ) (hb : 0 < b) : Integrable (fun y : ℝ => Real.exp (-b * (1 + y ^ 2))) := by
  simp_rw [Efac]
  exact (integrable_exp_neg_mul_sq hb).const_mul _

lemma hE2 (b : ℝ) (hb : 0 < b) : Integrable (fun y : ℝ => y ^ 2 * Real.exp (-b * (1 + y ^ 2))) := by
  simp_rw [Efac, ← mul_assoc, mul_comm (_ ^ 2) (Real.exp (-b)), mul_assoc]
  have := integrable_rpow_mul_exp_neg_mul_sq hb (s := 2) (by norm_num)
  simp only [Real.rpow_two] at this
  exact this.const_mul _

lemma g0 (b : ℝ) (hb : 0 < b) : ∫ y : ℝ, Real.exp (-b * (1 + y ^ 2)) = Real.exp (-b) * √(π / b) := by
  simp_rw [Efac]
  rw [integral_const_mul, integral_gaussian]

lemma g2 (b : ℝ) (hb : 0 < b) :
    ∫ y : ℝ, y ^ 2 * Real.exp (-b * (1 + y ^ 2)) = Real.exp (-b) * (√(π / b) / (2 * b)) := by
  simp_rw [Efac, ← mul_assoc, mul_comm (_ ^ 2) (Real.exp (-b)), mul_assoc]
  rw [integral_const_mul, gauss2 b hb]

lemma Pint (b : ℝ) (hb : 0 < b) (c0 c2 : ℝ) :
    ∫ y : ℝ, (c0 + c2 * y ^ 2) * Real.exp (-b * (1 + y ^ 2)) =
      c0 * (Real.exp (-b) * √(π / b)) + c2 * (Real.exp (-b) * (√(π / b) / (2 * b))) := by
  have : ∀ y : ℝ, (c0 + c2 * y ^ 2) * Real.exp (-b * (1 + y ^ 2)) =
      c0 * Real.exp (-b * (1 + y ^ 2)) + c2 * (y ^ 2 * Real.exp (-b * (1 + y ^ 2))) := by
    intro y; ring
  simp_rw [this]
  rw [integral_add ((hE b hb).const_mul c0) ((hE2 b hb).const_mul c2), integral_const_mul,
    integral_const_mul, g0 b hb, g2 b hb]

lemma intO (b : ℝ) (hb : 0 < b) (h : ℝ → ℝ) (C : ℝ) (hc : Continuous h)
    (hbd : ∀ y, |h y| ≤ C * (1 + y ^ 2)) :
    Integrable (fun y : ℝ => h y * Real.exp (-b * (1 + y ^ 2))) := by
  have hg : Integrable (fun y : ℝ => C * ((1 + y ^ 2) * Real.exp (-b * (1 + y ^ 2)))) := by
    have : ∀ y : ℝ, (1 + y ^ 2) * Real.exp (-b * (1 + y ^ 2)) =
        Real.exp (-b * (1 + y ^ 2)) + y ^ 2 * Real.exp (-b * (1 + y ^ 2)) := by intro y; ring
    simp_rw [this]
    exact ((hE b hb).add (hE2 b hb)).const_mul C
  refine hg.mono' ((hc.mul (by fun_prop)).aestronglyMeasurable) (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc |h y| * Real.exp (-b * (1 + y ^ 2)) ≤ (C * (1 + y ^ 2)) * Real.exp (-b * (1 + y ^ 2)) :=
        mul_le_mul_of_nonneg_right (hbd y) (Real.exp_pos _).le
    _ = _ := by ring

lemma oddzero (O : ℝ → ℝ) (hodd : ∀ y, O (-y) = -O y) : ∫ y : ℝ, O y = 0 := by
  have h := integral_neg_eq_self O volume
  simp_rw [hodd] at h
  rw [integral_neg] at h
  linarith

lemma split_odd (P O : ℝ → ℝ) (hP : Integrable P) (hO : Integrable O) (hodd : ∀ y, O (-y) = -O y) :
    ∫ y : ℝ, (P y + O y) = ∫ y : ℝ, P y := by
  rw [integral_add hP hO, oddzero O hodd, add_zero]

lemma tc : Continuous (fun y : ℝ => y / √(1 + y ^ 2)) :=
  continuous_id.div (by fun_prop) (fun y => (r_pos y).ne')

lemma t_abs (y : ℝ) : |y / √(1 + y ^ 2)| ≤ 1 := by
  have hr := r_pos y
  rw [abs_div, abs_of_pos hr, div_le_one hr]
  exact Real.abs_le_sqrt (by linarith [sq_nonneg y])

lemma ht2 (y : ℝ) : (1 + y ^ 2) * (y / √(1 + y ^ 2)) ^ 2 = y ^ 2 := by
  have hr := r_pos y
  have hs := r_sq y
  rw [div_pow, hs]; field_simp

lemma t_odd (y : ℝ) : (-y) / √(1 + (-y) ^ 2) = -(y / √(1 + y ^ 2)) := by
  rw [neg_sq, neg_div]

lemma K10 (l : ℝ) (hl : 0 < l) :
    ∫ u in (0 : ℝ)..1, u ^ (-(1 / 2 : ℝ) - ((1 : ℕ) : ℝ)) * (1 - u) ^ (-(1 / 2 : ℝ) - ((0 : ℕ) : ℝ)) *
        Real.exp (-(l ^ 2) / (2 * u * (1 - u))) =
      2 * (Real.exp (-(2 * l ^ 2)) * √(π / (2 * l ^ 2))) := by
  rw [Kgen]
  have hb : 0 < 2 * l ^ 2 := by positivity
  have hpt : ∀ y : ℝ, (1 / (1 + y ^ 2)) * (2 * (1 + y ^ 2) * (1 + y / √(1 + y ^ 2))) ^ 1 *
      (2 * (1 + y ^ 2) * (1 - y / √(1 + y ^ 2))) ^ 0 * Real.exp (-(2 * l ^ 2) * (1 + y ^ 2)) =
      (2 + 0 * y ^ 2) * Real.exp (-(2 * l ^ 2) * (1 + y ^ 2)) +
        (2 * (y / √(1 + y ^ 2))) * Real.exp (-(2 * l ^ 2) * (1 + y ^ 2)) := by
    intro y; rw [F_conv, A10 _ _ (rel y)]; ring
  simp_rw [hpt]
  rw [split_odd _ _ ((hE _ hb).const_mul 2 |>.congr (Filter.Eventually.of_forall fun y => by simp))
    (intO _ hb (fun y => 2 * (y / √(1 + y ^ 2))) 2 (continuous_const.mul tc)
      (fun y => by
        rw [abs_mul, abs_two]
        have := t_abs y
        nlinarith [sq_nonneg y]))
    (fun y => by rw [neg_sq, neg_div]; ring)]
  rw [Pint _ hb]
  ring

lemma sq_const (l : ℝ) (hl : 0 < l) : l / √(2 * π) * √(π / (2 * l ^ 2)) = 1 / 2 := by
  have h1 : √(π / (2 * l ^ 2)) = √π / (√2 * l) := by
    rw [Real.sqrt_div Real.pi_pos.le, Real.sqrt_mul (by norm_num), Real.sqrt_sq hl.le]
  rw [h1, Real.sqrt_mul (by norm_num)]
  have : 0 < √π := Real.sqrt_pos.2 Real.pi_pos
  have : 0 < √(2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have h2 : √(2 : ℝ) * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  field_simp
  linarith

lemma oddint (l : ℝ) (hb : 0 < 2 * l ^ 2) (C : ℝ) (h : ℝ → ℝ) (hc : Continuous h)
    (hbd : ∀ y, |h y| ≤ C * (1 + y ^ 2)) (hodd : ∀ y, h (-y) = -h y) (P : ℝ → ℝ)
    (hP : Integrable P) :
    ∫ y : ℝ, (P y + h y * Real.exp (-(2 * l ^ 2) * (1 + y ^ 2))) = ∫ y : ℝ, P y :=
  split_odd _ _ hP (intO _ hb h C hc hbd)
    (fun y => by rw [hodd, neg_sq]; ring)

lemma K11 (l : ℝ) (hl : 0 < l) :
    ∫ u in (0 : ℝ)..1, u ^ (-(1 / 2 : ℝ) - ((1 : ℕ) : ℝ)) * (1 - u) ^ (-(1 / 2 : ℝ) - ((1 : ℕ) : ℝ)) *
        Real.exp (-(l ^ 2) / (2 * u * (1 - u))) =
      4 * (Real.exp (-(2 * l ^ 2)) * √(π / (2 * l ^ 2))) +
        0 * (Real.exp (-(2 * l ^ 2)) * (√(π / (2 * l ^ 2)) / (2 * (2 * l ^ 2)))) := by
  rw [Kgen]
  have hb : 0 < 2 * l ^ 2 := by positivity
  have hpt : ∀ y : ℝ, (1 / (1 + y ^ 2)) * (2 * (1 + y ^ 2) * (1 + y / √(1 + y ^ 2))) ^ 1 *
      (2 * (1 + y ^ 2) * (1 - y / √(1 + y ^ 2))) ^ 1 * Real.exp (-(2 * l ^ 2) * (1 + y ^ 2)) =
      (4 + 0 * y ^ 2) * Real.exp (-(2 * l ^ 2) * (1 + y ^ 2)) := by
    intro y; rw [F_conv, A11 _ _ (rel y)]; ring
  simp_rw [hpt]
  exact Pint _ hb 4 0

lemma K20 (l : ℝ) (hl : 0 < l) :
    ∫ u in (0 : ℝ)..1, u ^ (-(1 / 2 : ℝ) - ((2 : ℕ) : ℝ)) * (1 - u) ^ (-(1 / 2 : ℝ) - ((0 : ℕ) : ℝ)) *
        Real.exp (-(l ^ 2) / (2 * u * (1 - u))) =
      4 * (Real.exp (-(2 * l ^ 2)) * √(π / (2 * l ^ 2))) +
        8 * (Real.exp (-(2 * l ^ 2)) * (√(π / (2 * l ^ 2)) / (2 * (2 * l ^ 2)))) := by
  rw [Kgen]
  have hb : 0 < 2 * l ^ 2 := by positivity
  have hpt : ∀ y : ℝ, (1 / (1 + y ^ 2)) * (2 * (1 + y ^ 2) * (1 + y / √(1 + y ^ 2))) ^ 2 *
      (2 * (1 + y ^ 2) * (1 - y / √(1 + y ^ 2))) ^ 0 * Real.exp (-(2 * l ^ 2) * (1 + y ^ 2)) =
      (4 + 8 * y ^ 2) * Real.exp (-(2 * l ^ 2) * (1 + y ^ 2)) +
        (8 * ((1 + y ^ 2) * (y / √(1 + y ^ 2)))) * Real.exp (-(2 * l ^ 2) * (1 + y ^ 2)) := by
    intro y
    rw [F_conv, A20 _ _ (rel y), r_sq y]
    linear_combination (4 * Real.exp (-(2 * l ^ 2) * (1 + y ^ 2))) * ht2 y
  simp_rw [hpt]
  rw [oddint l hb 8 (fun y => 8 * ((1 + y ^ 2) * (y / √(1 + y ^ 2))))
    (by have := tc; fun_prop)
    (fun y => by
      rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 + y ^ 2), abs_of_pos (by norm_num : (0:ℝ) < 8)]
      have := t_abs y
      nlinarith [sq_nonneg y])
    (fun y => by simp only [t_odd, neg_sq]; ring) _ ((hE _ hb).const_mul 4 |>.add ((hE2 _ hb).const_mul 8) |>.congr
      (Filter.Eventually.of_forall fun y => by simp only [Pi.add_apply]; ring))]
  exact Pint _ hb 4 8

lemma K21 (l : ℝ) (hl : 0 < l) :
    ∫ u in (0 : ℝ)..1, u ^ (-(1 / 2 : ℝ) - ((2 : ℕ) : ℝ)) * (1 - u) ^ (-(1 / 2 : ℝ) - ((1 : ℕ) : ℝ)) *
        Real.exp (-(l ^ 2) / (2 * u * (1 - u))) =
      8 * (Real.exp (-(2 * l ^ 2)) * √(π / (2 * l ^ 2))) +
        8 * (Real.exp (-(2 * l ^ 2)) * (√(π / (2 * l ^ 2)) / (2 * (2 * l ^ 2)))) := by
  rw [Kgen]
  have hb : 0 < 2 * l ^ 2 := by positivity
  have hpt : ∀ y : ℝ, (1 / (1 + y ^ 2)) * (2 * (1 + y ^ 2) * (1 + y / √(1 + y ^ 2))) ^ 2 *
      (2 * (1 + y ^ 2) * (1 - y / √(1 + y ^ 2))) ^ 1 * Real.exp (-(2 * l ^ 2) * (1 + y ^ 2)) =
      (8 + 8 * y ^ 2) * Real.exp (-(2 * l ^ 2) * (1 + y ^ 2)) +
        (8 * ((1 + y ^ 2) * (y / √(1 + y ^ 2)))) * Real.exp (-(2 * l ^ 2) * (1 + y ^ 2)) := by
    intro y
    rw [F_conv, A21 _ _ (rel y), r_sq y]
    ring
  simp_rw [hpt]
  rw [oddint l hb 8 (fun y => 8 * ((1 + y ^ 2) * (y / √(1 + y ^ 2))))
    (by have := tc; fun_prop)
    (fun y => by
      rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 + y ^ 2), abs_of_pos (by norm_num : (0:ℝ) < 8)]
      have := t_abs y
      nlinarith [sq_nonneg y])
    (fun y => by simp only [t_odd, neg_sq]; ring) _ ((hE _ hb).const_mul 8 |>.add ((hE2 _ hb).const_mul 8) |>.congr
      (Filter.Eventually.of_forall fun y => by simp only [Pi.add_apply]; ring))]
  exact Pint _ hb 8 8

lemma K22 (l : ℝ) (hl : 0 < l) :
    ∫ u in (0 : ℝ)..1, u ^ (-(1 / 2 : ℝ) - ((2 : ℕ) : ℝ)) * (1 - u) ^ (-(1 / 2 : ℝ) - ((2 : ℕ) : ℝ)) *
        Real.exp (-(l ^ 2) / (2 * u * (1 - u))) =
      16 * (Real.exp (-(2 * l ^ 2)) * √(π / (2 * l ^ 2))) +
        16 * (Real.exp (-(2 * l ^ 2)) * (√(π / (2 * l ^ 2)) / (2 * (2 * l ^ 2)))) := by
  rw [Kgen]
  have hb : 0 < 2 * l ^ 2 := by positivity
  have hpt : ∀ y : ℝ, (1 / (1 + y ^ 2)) * (2 * (1 + y ^ 2) * (1 + y / √(1 + y ^ 2))) ^ 2 *
      (2 * (1 + y ^ 2) * (1 - y / √(1 + y ^ 2))) ^ 2 * Real.exp (-(2 * l ^ 2) * (1 + y ^ 2)) =
      (16 + 16 * y ^ 2) * Real.exp (-(2 * l ^ 2) * (1 + y ^ 2)) := by
    intro y
    rw [F_conv, A22 _ _ (rel y), r_sq y]
    ring
  simp_rw [hpt]
  exact Pint _ hb 16 16

lemma Ifin (l : ℝ) (hl : 0 < l) (K c0 c2 : ℝ)
    (hK : K = c0 * (Real.exp (-(2 * l ^ 2)) * √(π / (2 * l ^ 2))) +
        c2 * (Real.exp (-(2 * l ^ 2)) * (√(π / (2 * l ^ 2)) / (2 * (2 * l ^ 2))))) :
    l * Real.exp (2 * l ^ 2) / √(2 * π) * K = (c0 + c2 / (4 * l ^ 2)) / 2 := by
  have hc := sq_const l hl
  have he : Real.exp (2 * l ^ 2) * Real.exp (-(2 * l ^ 2)) = 1 := by
    rw [← Real.exp_add]; simp
  calc l * Real.exp (2 * l ^ 2) / √(2 * π) * K
      = (l / √(2 * π) * √(π / (2 * l ^ 2))) * (Real.exp (2 * l ^ 2) * Real.exp (-(2 * l ^ 2))) *
          (c0 + c2 / (4 * l ^ 2)) := by
        rw [hK]; field_simp; ring
    _ = _ := by rw [hc, he]; ring

end CsLib

open CsLib in
theorem solution (l : ℝ) (hl : 0 < l) :
    I 1 1 l / 2 = 1 ∧ I 1 0 l = 1 ∧ I 2 2 l / 2 = 4 + 1 / l ^ 2 ∧ I 2 1 l = 4 + 1 / l ^ 2 ∧
      I 2 0 l = 2 + 1 / l ^ 2 := by
  have h11 := K11 l hl
  have h10 := K10 l hl
  have h22 := K22 l hl
  have h21 := K21 l hl
  have h20 := K20 l hl
  simp only [Nat.cast_one, Nat.cast_zero, Nat.cast_ofNat] at h11 h10 h22 h21 h20
  have hl2 : l ^ 2 ≠ 0 := by positivity
  unfold I
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [Ifin l hl _ 4 0 h11]; field_simp; try ring
  · rw [Ifin l hl _ 2 0 (by rw [h10]; ring)]; field_simp; try ring
  · rw [Ifin l hl _ 16 16 h22]; field_simp; try ring
  · rw [Ifin l hl _ 8 8 h21]; field_simp; try ring
  · rw [Ifin l hl _ 4 8 h20]; field_simp; try ring
