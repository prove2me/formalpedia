-- Prove2me | solution 1 for LanglandsTunnell.add_pow_mul_apply_neg_eq_mul_mulConvGaussian_of_mellin_sheet_eq_archFactor
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/fe6b1b85-f6a8-5b1b-b399-7929028a8ea1

import Definitions.Def_LanglandsTunnell_ArchParam
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.MellinInversion
import Theorems.Thm_LanglandsTunnell_mellin_mulConvGaussian_eq_archFactor_principal
import Theorems.Thm_Complex_exists_forall_norm_Gamma_le_mul_exp_and_exp_le_mul_norm_Gamma_of_re_mem_Icc_of_one_le_abs_im
import Theorems.Thm_LanglandsTunnell_mellinConvergent_and_mellin_ofReal_pos_rpow_mul_exp_neg_mul_sq_add_inv_sq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_add_pow_mul_apply_neg_eq_mul_mulConvGaussian_of_mellin_sheet_eq_archFactor

set_option autoImplicit false

open scoped Real
open LanglandsTunnell

namespace K9sheet

open Complex MeasureTheory Set Filter Real

noncomputable def G (p q : ℂ) (t : ℝ) : ℂ :=
  (4 : ℂ) * ∫ r in Ioi (0 : ℝ),
    ((r : ℂ) ^ p * (Real.exp (-(π * r ^ 2)) : ℂ)) * (((t / r : ℝ) : ℂ) ^ q * (Real.exp (-(π * (t / r) ^ 2)) : ℂ)) / (r : ℂ)

theorem archFactor_principal (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2) (s : ℂ) :
    (RealArchParam.principal u₁ a₁ u₂ a₂).archFactor s =
      Gammaℝ (s + (u₁ + signShift a₁)) * Gammaℝ (s + (u₂ + signShift a₂)) := by
  simp [RealArchParam.archFactor, RealArchParam.gammaR, RealArchParam.gammaC]

theorem twist_zero_principal (u₁ u₂ : ℂ) (a₁ a₂ b : ZMod 2) :
    (RealArchParam.principal u₁ a₁ u₂ a₂).twist 0 b = RealArchParam.principal u₁ (a₁ + b) u₂ (a₂ + b) := by
  simp [RealArchParam.twist]

theorem mellin_G (u₁ u₂ : ℂ) (a₁ a₂ b : ZMod 2) (s : ℂ)
    (h₁ : 0 < (s + (u₁ + signShift (a₁ + b))).re) (h₂ : 0 < (s + (u₂ + signShift (a₂ + b))).re) :
    mellin (G (u₁ + signShift (a₁ + b)) (u₂ + signShift (a₂ + b))) s =
      ((RealArchParam.principal u₁ a₁ u₂ a₂).twist 0 b).archFactor s := by
  rw [twist_zero_principal]
  exact LanglandsTunnell.mellin_mulConvGaussian_eq_archFactor_principal u₁ (a₁ + b) u₂ (a₂ + b) s h₁ h₂

theorem archFactor_ne_zero (u₁ u₂ : ℂ) (a₁ a₂ b : ZMod 2) (s : ℂ)
    (h₁ : 0 < (s + (u₁ + signShift (a₁ + b))).re) (h₂ : 0 < (s + (u₂ + signShift (a₂ + b))).re) :
    ((RealArchParam.principal u₁ a₁ u₂ a₂).twist 0 b).archFactor s ≠ 0 := by
  rw [twist_zero_principal, archFactor_principal]
  exact mul_ne_zero (Gammaℝ_ne_zero_of_re_pos h₁) (Gammaℝ_ne_zero_of_re_pos h₂)

theorem mellinConvergent_of_mellin_ne_zero {f : ℝ → ℂ} {s : ℂ} (h : mellin f s ≠ 0) :
    MellinConvergent f s := by
  by_contra hc
  exact h (integral_undef hc)

theorem mellinInv_congr (σ : ℝ) {φ₁ φ₂ : ℂ → ℂ} (h : ∀ y : ℝ, φ₁ (σ + y * I) = φ₂ (σ + y * I)) (x : ℝ) :
    mellinInv σ φ₁ x = mellinInv σ φ₂ x := by
  simp only [mellinInv, h]

theorem integrable_exp_neg_mul_abs {c : ℝ} (hc : 0 < c) :
    Integrable fun y : ℝ => Real.exp (-c * |y|) := by
  have h1 : IntegrableOn (fun y : ℝ => Real.exp (-c * |y|)) (Iic 0) := by
    refine (integrableOn_congr_fun (fun y hy => ?_) measurableSet_Iic).mpr (integrableOn_exp_mul_Iic hc 0)
    show Real.exp (-c * |y|) = Real.exp (c * y)
    rw [abs_of_nonpos hy]; ring_nf
  have h2 : IntegrableOn (fun y : ℝ => Real.exp (-c * |y|)) (Ioi 0) := by
    refine (integrableOn_congr_fun (fun y hy => ?_) measurableSet_Ioi).mpr (exp_neg_integrableOn_Ioi 0 hc)
    show Real.exp (-c * |y|) = Real.exp (-c * y)
    rw [abs_of_pos hy]
  have h := h1.union h2
  rwa [Iic_union_Ioi, integrableOn_univ] at h

theorem pow_mul_exp_le (N : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, 0 ≤ u →
    (1 + u) ^ N * Real.exp (-(π / 2) * u) ≤ C * Real.exp (-(π / 4) * u) := by
  set c : ℝ := π / 4 with hc_def
  have hc : 0 < c := by positivity
  refine ⟨c⁻¹ ^ N * N.factorial * Real.exp c, by positivity, fun u hu => ?_⟩
  have hN : (0 : ℝ) < N.factorial := by positivity
  have h1 : (c * (1 + u)) ^ N / N.factorial ≤ Real.exp (c * (1 + u)) :=
    Real.pow_div_factorial_le_exp (c * (1 + u)) (by positivity) N
  rw [div_le_iff₀ hN] at h1
  have h2 : (1 + u) ^ N ≤ c⁻¹ ^ N * N.factorial * Real.exp (c * (1 + u)) := by
    calc (1 + u) ^ N = c⁻¹ ^ N * (c * (1 + u)) ^ N := by
          rw [← mul_pow, ← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
      _ ≤ c⁻¹ ^ N * (Real.exp (c * (1 + u)) * N.factorial) := by gcongr
      _ = _ := by ring
  have h3 : Real.exp (c * (1 + u)) * Real.exp (-(π / 2) * u) = Real.exp c * Real.exp (-(π / 4) * u) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    rw [hc_def]; ring
  calc (1 + u) ^ N * Real.exp (-(π / 2) * u)
      ≤ (c⁻¹ ^ N * N.factorial * Real.exp (c * (1 + u))) * Real.exp (-(π / 2) * u) := by gcongr
    _ = c⁻¹ ^ N * N.factorial * (Real.exp (c * (1 + u)) * Real.exp (-(π / 2) * u)) := by ring
    _ = c⁻¹ ^ N * N.factorial * Real.exp c * Real.exp (-(π / 4) * u) := by rw [h3]; ring

theorem norm_Gamma_vertical_le {x : ℝ} (hx : 0 < x) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y : ℝ, ‖Complex.Gamma ((x : ℂ) + (y : ℂ) * I)‖ ≤ K * Real.exp (-(π / 4) * |y|) := by
  obtain ⟨A, N, hAN⟩ :=
    Complex.exists_forall_norm_Gamma_le_mul_exp_and_exp_le_mul_norm_Gamma_of_re_mem_Icc_of_one_le_abs_im x x
  obtain ⟨C, hC0, hC⟩ := pow_mul_exp_le N
  have hcont : Continuous fun y : ℝ => Complex.Gamma ((x : ℂ) + (y : ℂ) * I) := by
    refine continuous_iff_continuousAt.mpr fun y => ?_
    have hne : ∀ m : ℕ, (x : ℂ) + (y : ℂ) * I ≠ -(m : ℂ) := by
      intro m h
      have := congrArg Complex.re h
      simp at this
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    exact ContinuousAt.comp (g := Complex.Gamma) (f := fun y : ℝ => (x : ℂ) + (y : ℂ) * I)
      (Complex.differentiableAt_Gamma _ hne).continuousAt
      (by fun_prop : Continuous fun y : ℝ => (x : ℂ) + (y : ℂ) * I).continuousAt
  obtain ⟨B, hB⟩ := (isCompact_Icc : IsCompact (Icc (-1 : ℝ) 1)).exists_bound_of_continuousOn hcont.continuousOn
  have hA : 0 ≤ A := by
    have h := (hAN ((x : ℂ) + (1 : ℝ) * I) (by simp) (by simp) (by simp)).2
    have hpos : 0 < Real.exp (-(Real.pi / 2) * |((x : ℂ) + ((1 : ℝ) : ℂ) * I).im|) := Real.exp_pos _
    by_contra hA
    have : A * (1 + |((x : ℂ) + ((1 : ℝ) : ℂ) * I).im|) ^ N * ‖Complex.Gamma ((x : ℂ) + ((1 : ℝ) : ℂ) * I)‖ ≤ 0 := by
      have : 0 ≤ (1 + |((x : ℂ) + ((1 : ℝ) : ℂ) * I).im|) ^ N * ‖Complex.Gamma ((x : ℂ) + ((1 : ℝ) : ℂ) * I)‖ := by
        positivity
      nlinarith
    linarith
  refine ⟨max (A * C) (B * Real.exp (π / 4)), le_max_of_le_right (by
    have := le_trans (norm_nonneg _) (hB 0 (by simp)); positivity), fun y => ?_⟩
  rcases le_or_gt 1 |y| with hy | hy
  · have h := (hAN ((x : ℂ) + (y : ℂ) * I) (by simp) (by simp) (by simpa using hy)).1
    have him : ((x : ℂ) + (y : ℂ) * I).im = y := by simp
    rw [him] at h
    calc ‖Complex.Gamma ((x : ℂ) + (y : ℂ) * I)‖ ≤ A * (1 + |y|) ^ N * Real.exp (-(π / 2) * |y|) := h
      _ = A * ((1 + |y|) ^ N * Real.exp (-(π / 2) * |y|)) := by ring
      _ ≤ A * (C * Real.exp (-(π / 4) * |y|)) := mul_le_mul_of_nonneg_left (hC |y| (abs_nonneg y)) hA
      _ = (A * C) * Real.exp (-(π / 4) * |y|) := by ring
      _ ≤ _ := by gcongr; exact le_max_left _ _
  · have hmem : y ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [(abs_lt.mp hy).1], by linarith [(abs_lt.mp hy).2]⟩
    have h := hB y hmem
    have hB0 : 0 ≤ B := le_trans (norm_nonneg _) h
    have hone : 1 ≤ Real.exp (π / 4) * Real.exp (-(π / 4) * |y|) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by nlinarith [abs_nonneg y, Real.pi_pos])
    calc ‖Complex.Gamma ((x : ℂ) + (y : ℂ) * I)‖ ≤ B := h
      _ ≤ B * (Real.exp (π / 4) * Real.exp (-(π / 4) * |y|)) := le_mul_of_one_le_right hB0 hone
      _ = (B * Real.exp (π / 4)) * Real.exp (-(π / 4) * |y|) := by ring
      _ ≤ _ := by gcongr; exact le_max_right _ _

theorem norm_Gammaℝ_vertical_le {z : ℂ} (hz : 0 < z.re) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y : ℝ, ‖Gammaℝ (z + (y : ℂ) * I)‖ ≤ K * Real.exp (-(π / 8) * |y|) := by
  obtain ⟨K, hK0, hK⟩ := norm_Gamma_vertical_le (half_pos hz)
  refine ⟨π ^ (-z.re / 2) * K * Real.exp ((π / 8) * |z.im|), by positivity, fun y => ?_⟩
  rw [Gammaℝ_def, norm_mul]
  have hπ : ‖(π : ℂ) ^ (-(z + (y : ℂ) * I) / 2)‖ = π ^ (-z.re / 2) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    congr 1
    simp
  have harg : (z + (y : ℂ) * I) / 2 = ((z.re / 2 : ℝ) : ℂ) + (((z.im + y) / 2 : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp
  rw [hπ, harg]
  have hexp : Real.exp (-(π / 4) * |(z.im + y) / 2|) ≤ Real.exp ((π / 8) * |z.im|) * Real.exp (-(π / 8) * |y|) := by
    rw [← Real.exp_add, Real.exp_le_exp, abs_div, abs_two]
    have : |y| ≤ |z.im + y| + |z.im| := by
      calc |y| = |(z.im + y) - z.im| := by ring_nf
        _ ≤ |z.im + y| + |z.im| := abs_sub _ _
    nlinarith [Real.pi_pos, this]
  calc π ^ (-z.re / 2) * ‖Complex.Gamma (((z.re / 2 : ℝ) : ℂ) + (((z.im + y) / 2 : ℝ) : ℂ) * I)‖
      ≤ π ^ (-z.re / 2) * (K * Real.exp (-(π / 4) * |(z.im + y) / 2|)) := by gcongr; exact hK _
    _ ≤ π ^ (-z.re / 2) * (K * (Real.exp ((π / 8) * |z.im|) * Real.exp (-(π / 8) * |y|))) := by gcongr
    _ = _ := by ring

theorem continuous_Gammaℝ_vertical {z : ℂ} (hz : 0 < z.re) :
    Continuous fun y : ℝ => Gammaℝ (z + (y : ℂ) * I) := by
  have hline : Continuous fun y : ℝ => z + (y : ℂ) * I := by fun_prop
  refine continuous_iff_continuousAt.mpr fun y => ?_
  have h1 : ContinuousAt (fun s : ℂ => (π : ℂ) ^ (-s / 2)) (z + (y : ℂ) * I) :=
    ContinuousAt.const_cpow (by fun_prop : Continuous fun s : ℂ => -s / 2).continuousAt
      (Or.inl (ofReal_ne_zero.mpr Real.pi_ne_zero))
  have h2 : ContinuousAt (fun s : ℂ => Complex.Gamma (s / 2)) (z + (y : ℂ) * I) := by
    have hne : ∀ m : ℕ, (z + (y : ℂ) * I) / 2 ≠ -(m : ℂ) := by
      intro m h
      have := congrArg Complex.re h
      simp at this
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    exact (Complex.differentiableAt_Gamma _ hne).continuousAt.comp (f := fun s : ℂ => s / 2)
      (by fun_prop : Continuous fun s : ℂ => s / 2).continuousAt
  have hG : ContinuousAt Gammaℝ (z + (y : ℂ) * I) := by
    have : Gammaℝ = fun s => (π : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) := funext Gammaℝ_def
    rw [this]
    exact h1.mul h2
  exact ContinuousAt.comp (g := Gammaℝ) (f := fun y : ℝ => z + (y : ℂ) * I) hG hline.continuousAt

theorem verticalIntegrable_archFactor (u₁ u₂ : ℂ) (a₁ a₂ b : ZMod 2) (σ : ℝ)
    (h₁ : 0 < σ + (u₁ + signShift (a₁ + b)).re) (h₂ : 0 < σ + (u₂ + signShift (a₂ + b)).re) :
    Integrable fun y : ℝ => ((RealArchParam.principal u₁ a₁ u₂ a₂).twist 0 b).archFactor ((σ : ℂ) + (y : ℂ) * I) := by
  simp only [twist_zero_principal, archFactor_principal]
  set z₁ : ℂ := (σ : ℂ) + (u₁ + signShift (a₁ + b)) with hz₁
  set z₂ : ℂ := (σ : ℂ) + (u₂ + signShift (a₂ + b)) with hz₂
  have hfun : (fun y : ℝ => Gammaℝ ((σ : ℂ) + (y : ℂ) * I + (u₁ + signShift (a₁ + b))) *
      Gammaℝ ((σ : ℂ) + (y : ℂ) * I + (u₂ + signShift (a₂ + b)))) =
      fun y : ℝ => Gammaℝ (z₁ + (y : ℂ) * I) * Gammaℝ (z₂ + (y : ℂ) * I) := by
    funext y; rw [hz₁, hz₂]; ring_nf
  rw [hfun]
  have hre₁ : 0 < z₁.re := by rw [hz₁, add_re, ofReal_re]; exact h₁
  have hre₂ : 0 < z₂.re := by rw [hz₂, add_re, ofReal_re]; exact h₂
  obtain ⟨K₁, hK₁0, hK₁⟩ := norm_Gammaℝ_vertical_le hre₁
  obtain ⟨K₂, hK₂0, hK₂⟩ := norm_Gammaℝ_vertical_le hre₂
  refine Integrable.mono' ((integrable_exp_neg_mul_abs (by positivity : (0 : ℝ) < π / 4)).const_mul (K₁ * K₂))
    ((continuous_Gammaℝ_vertical hre₁).mul (continuous_Gammaℝ_vertical hre₂)).aestronglyMeasurable
    (ae_of_all _ fun y => ?_)
  rw [norm_mul]
  calc ‖Gammaℝ (z₁ + (y : ℂ) * I)‖ * ‖Gammaℝ (z₂ + (y : ℂ) * I)‖
      ≤ (K₁ * Real.exp (-(π / 8) * |y|)) * (K₂ * Real.exp (-(π / 8) * |y|)) :=
        mul_le_mul (hK₁ y) (hK₂ y) (norm_nonneg _) (by positivity)
    _ = K₁ * K₂ * Real.exp (-(π / 4) * |y|) := by
        rw [mul_mul_mul_comm, ← Real.exp_add]
        congr 1
        ring

noncomputable def Φ (p q : ℂ) (t r : ℝ) : ℂ :=
  ((r : ℂ) ^ p * (Real.exp (-(π * r ^ 2)) : ℂ)) * (((t / r : ℝ) : ℂ) ^ q * (Real.exp (-(π * (t / r) ^ 2)) : ℂ)) / (r : ℂ)

theorem G_eq_integral_Φ (p q : ℂ) : G p q = fun t => (4 : ℂ) * ∫ r in Ioi (0 : ℝ), Φ p q t r := rfl

theorem norm_Φ (p q : ℂ) {t r : ℝ} (ht : 0 < t) (hr : 0 < r) :
    ‖Φ p q t r‖ = r ^ p.re * Real.exp (-(π * r ^ 2)) * ((t / r) ^ q.re * Real.exp (-(π * (t / r) ^ 2))) / r := by
  have htr : 0 < t / r := div_pos ht hr
  simp only [Φ, norm_div, norm_mul, norm_cpow_eq_rpow_re_of_pos hr, norm_cpow_eq_rpow_re_of_pos htr,
    Complex.norm_of_nonneg (Real.exp_pos _).le, Complex.norm_of_nonneg hr.le]

theorem norm_Φ_le (p q : ℂ) {x t r : ℝ} (hx : 0 < x) (ht : t ∈ Icc (x / 2) (2 * x)) (hr : 0 < r) :
    ‖Φ p q t r‖ ≤ ((x / 2) ^ q.re + (2 * x) ^ q.re) *
      (r ^ (p.re - q.re - 1) * Real.exp (-(π * r ^ 2 + π * (x / 2) ^ 2 * (r ^ 2)⁻¹))) := by
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht.1
  rw [norm_Φ p q ht0 hr, Real.div_rpow ht0.le hr.le]
  have hM : t ^ q.re ≤ (x / 2) ^ q.re + (2 * x) ^ q.re := by
    rcases le_or_gt 0 q.re with h | h
    · calc t ^ q.re ≤ (2 * x) ^ q.re := Real.rpow_le_rpow ht0.le ht.2 h
        _ ≤ _ := le_add_of_nonneg_left (Real.rpow_nonneg (by positivity) _)
    · calc t ^ q.re ≤ (x / 2) ^ q.re := Real.rpow_le_rpow_of_nonpos (by positivity) ht.1 h.le
        _ ≤ _ := le_add_of_nonneg_right (Real.rpow_nonneg (by positivity) _)
  have hE : Real.exp (-(π * (t / r) ^ 2)) ≤ Real.exp (-(π * (x / 2) ^ 2 * (r ^ 2)⁻¹)) := by
    rw [Real.exp_le_exp]
    have h2 : (x / 2) ^ 2 * (r ^ 2)⁻¹ ≤ (t / r) ^ 2 := by
      rw [div_pow t r, div_eq_mul_inv (t ^ 2)]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) ht.1 2) (by positivity)
    nlinarith [Real.pi_pos, h2]
  have hsplit : Real.exp (-(π * r ^ 2 + π * (x / 2) ^ 2 * (r ^ 2)⁻¹)) =
      Real.exp (-(π * r ^ 2)) * Real.exp (-(π * (x / 2) ^ 2 * (r ^ 2)⁻¹)) := by
    rw [neg_add, Real.exp_add]
  have hpow : r ^ (p.re - q.re - 1) = r ^ p.re / r ^ q.re / r := by
    rw [Real.rpow_sub hr, Real.rpow_sub hr, Real.rpow_one]
  rw [hsplit, hpow]
  have hrq : 0 < r ^ q.re := Real.rpow_pos_of_pos hr _
  calc r ^ p.re * Real.exp (-(π * r ^ 2)) * (t ^ q.re / r ^ q.re * Real.exp (-(π * (t / r) ^ 2))) / r
      = (t ^ q.re * Real.exp (-(π * (t / r) ^ 2))) * (r ^ p.re * Real.exp (-(π * r ^ 2)) / r ^ q.re / r) := by
        field_simp
    _ ≤ (((x / 2) ^ q.re + (2 * x) ^ q.re) * Real.exp (-(π * (x / 2) ^ 2 * (r ^ 2)⁻¹))) *
          (r ^ p.re * Real.exp (-(π * r ^ 2)) / r ^ q.re / r) := by
        gcongr
    _ = _ := by ring

theorem integrableOn_majorant (α : ℝ) {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun r : ℝ => r ^ α * Real.exp (-(π * r ^ 2 + π * c ^ 2 * (r ^ 2)⁻¹))) (Ioi 0) := by
  set lam : ℝ := Real.sqrt c with hlam
  have hlam0 : 0 < lam := Real.sqrt_pos.mpr hc
  have hlam2 : lam ^ 2 = c := Real.sq_sqrt hc.le
  have hb : 0 < π * c := by positivity
  have h := (LanglandsTunnell.mellinConvergent_and_mellin_ofReal_pos_rpow_mul_exp_neg_mul_sq_add_inv_sq
    (π * c) hb 0).1 ((α + 1 : ℝ) : ℂ)
  rw [← MellinConvergent.comp_mul_left (inv_pos.mpr hlam0)] at h
  have h' := h.norm
  refine (integrableOn_congr_fun (fun r hr => ?_) measurableSet_Ioi).mp h'
  have hr : 0 < r := hr
  rw [norm_smul, show ((α + 1 : ℝ) : ℂ) - 1 = ((α : ℝ) : ℂ) by push_cast; ring,
    norm_cpow_eq_rpow_re_of_pos hr, ofReal_re, Complex.norm_of_nonneg (by positivity), Real.rpow_zero, one_mul]
  congr 1
  have hr2 : (lam⁻¹ * r) ^ 2 = r ^ 2 / c := by rw [mul_pow, inv_pow, hlam2]; ring
  rw [hr2]
  field_simp

theorem continuousOn_Φ (p q : ℂ) {t : ℝ} (ht : 0 < t) : ContinuousOn (Φ p q t) (Ioi 0) := by
  intro r hr
  have hr : 0 < r := hr
  apply ContinuousAt.continuousWithinAt
  have h1 : ContinuousAt (fun r : ℝ => (r : ℂ) ^ p) r := continuousAt_ofReal_cpow_const r p (Or.inr hr.ne')
  have h2 : ContinuousAt (fun r : ℝ => ((Real.exp (-(π * r ^ 2)) : ℝ) : ℂ)) r :=
    (by fun_prop : Continuous fun r : ℝ => ((Real.exp (-(π * r ^ 2)) : ℝ) : ℂ)).continuousAt
  have hdiv : ContinuousAt (fun r : ℝ => t / r) r := continuousAt_const.div continuousAt_id hr.ne'
  have h3 : ContinuousAt (fun r : ℝ => ((t / r : ℝ) : ℂ) ^ q) r := by
    have hc : ContinuousAt (fun a : ℝ => (a : ℂ) ^ q) (t / r) :=
      continuousAt_ofReal_cpow_const (t / r) q (Or.inr (div_pos ht hr).ne')
    exact ContinuousAt.comp (g := fun a : ℝ => (a : ℂ) ^ q) hc hdiv
  have h4 : ContinuousAt (fun r : ℝ => ((Real.exp (-(π * (t / r) ^ 2)) : ℝ) : ℂ)) r := by
    have hc : Continuous fun a : ℝ => ((Real.exp (-(π * a ^ 2)) : ℝ) : ℂ) := by fun_prop
    exact ContinuousAt.comp (g := fun a : ℝ => ((Real.exp (-(π * a ^ 2)) : ℝ) : ℂ)) hc.continuousAt hdiv
  have h5 : ContinuousAt (fun r : ℝ => (r : ℂ)) r := continuous_ofReal.continuousAt
  exact ((h1.mul h2).mul (h3.mul h4)).div h5 (ofReal_ne_zero.mpr hr.ne')

theorem continuousAt_Φ_left (p q : ℂ) {x r : ℝ} (hx : 0 < x) (hr : 0 < r) :
    ContinuousAt (fun t : ℝ => Φ p q t r) x := by
  have hdiv : ContinuousAt (fun t : ℝ => t / r) x := continuousAt_id.div continuousAt_const hr.ne'
  have h3 : ContinuousAt (fun t : ℝ => ((t / r : ℝ) : ℂ) ^ q) x := by
    have hc : ContinuousAt (fun a : ℝ => (a : ℂ) ^ q) (x / r) :=
      continuousAt_ofReal_cpow_const (x / r) q (Or.inr (div_pos hx hr).ne')
    exact ContinuousAt.comp (g := fun a : ℝ => (a : ℂ) ^ q) hc hdiv
  have h4 : ContinuousAt (fun t : ℝ => ((Real.exp (-(π * (t / r) ^ 2)) : ℝ) : ℂ)) x := by
    have hc : Continuous fun a : ℝ => ((Real.exp (-(π * a ^ 2)) : ℝ) : ℂ) := by fun_prop
    exact ContinuousAt.comp (g := fun a : ℝ => ((Real.exp (-(π * a ^ 2)) : ℝ) : ℂ)) hc.continuousAt hdiv
  exact ((continuousAt_const.mul (h3.mul h4)).div continuousAt_const (ofReal_ne_zero.mpr hr.ne'))

theorem continuousAt_G (p q : ℂ) {x : ℝ} (hx : 0 < x) : ContinuousAt (G p q) x := by
  have hΦ : ContinuousAt (fun t => ∫ r in Ioi (0 : ℝ), Φ p q t r) x := by
    refine continuousAt_of_dominated
      (bound := fun r => ((x / 2) ^ q.re + (2 * x) ^ q.re) *
        (r ^ (p.re - q.re - 1) * Real.exp (-(π * r ^ 2 + π * (x / 2) ^ 2 * (r ^ 2)⁻¹)))) ?_ ?_ ?_ ?_
    · filter_upwards [Ioi_mem_nhds hx] with t ht
      exact (continuousOn_Φ p q ht).aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [Icc_mem_nhds (by linarith : x / 2 < x) (by linarith : x < 2 * x)] with t ht
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      exact norm_Φ_le p q hx ht hr
    · exact (integrableOn_majorant (p.re - q.re - 1) (by positivity : 0 < x / 2)).const_mul _
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      exact continuousAt_Φ_left p q hx hr
  rw [G_eq_integral_Φ]
  exact continuousAt_const.mul hΦ

theorem main (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2) (W : ℝ → ℂ)
    (hWc : ContinuousOn W {t : ℝ | t ≠ 0}) (b : ZMod 2)
    (hMel : ∃ s₀ : ℝ, ∀ s : ℂ, s₀ < s.re →
      MellinConvergent (fun t : ℝ => (W t + (-1 : ℂ) ^ b.val * W (-t)) / (t : ℂ)) s ∧
        mellin (fun t : ℝ => (W t + (-1 : ℂ) ^ b.val * W (-t)) / (t : ℂ)) s
          = ((RealArchParam.principal u₁ a₁ u₂ a₂).twist 0 b).archFactor s)
    (t : ℝ) (ht : 0 < t) :
    W t + (-1 : ℂ) ^ b.val * W (-t) =
      (t : ℂ) * G (u₁ + signShift (a₁ + b)) (u₂ + signShift (a₂ + b)) t := by
  obtain ⟨s₀, hs₀⟩ := hMel
  set p : ℂ := u₁ + signShift (a₁ + b) with hp
  set q : ℂ := u₂ + signShift (a₂ + b) with hq
  set F : ℝ → ℂ := fun t : ℝ => (W t + (-1 : ℂ) ^ b.val * W (-t)) / (t : ℂ) with hF

  set σ : ℝ := max (s₀ + 1) (max (1 - p.re) (1 - q.re)) with hσ
  have hσ₀ : s₀ < σ := lt_of_lt_of_le (lt_add_one s₀) (le_max_left _ _)
  have hσp : 0 < σ + p.re := by
    have : 1 - p.re ≤ σ := (le_max_left _ _).trans (le_max_right _ _)
    linarith
  have hσq : 0 < σ + q.re := by
    have : 1 - q.re ≤ σ := (le_max_right _ _).trans (le_max_right _ _)
    linarith
  have hline : ∀ y : ℝ, s₀ < ((σ : ℂ) + (y : ℂ) * I).re ∧
      0 < (((σ : ℂ) + (y : ℂ) * I) + p).re ∧ 0 < (((σ : ℂ) + (y : ℂ) * I) + q).re := by
    intro y
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, mul_one,
      sub_zero, add_zero]
    exact ⟨by simpa using hσ₀, by linarith, by linarith⟩

  have hFG : ∀ y : ℝ, mellin F ((σ : ℂ) + (y : ℂ) * I) = mellin (G p q) ((σ : ℂ) + (y : ℂ) * I) := by
    intro y
    obtain ⟨h0, h1, h2⟩ := hline y
    rw [(hs₀ _ h0).2, hp, hq, mellin_G u₁ u₂ a₁ a₂ b _ h1 h2]

  have hσre : s₀ < ((σ : ℂ)).re := by simpa using hσ₀
  have hFconv : MellinConvergent F σ := (hs₀ (σ : ℂ) hσre).1
  have hFvert : VerticalIntegrable (mellin F) σ := by
    have hI := verticalIntegrable_archFactor u₁ u₂ a₁ a₂ b σ hσp hσq
    refine (integrable_congr (ae_of_all _ fun y => ?_)).mpr hI
    exact (hs₀ _ (hline y).1).2
  have hFcont : ContinuousAt F t := by
    have hW1 : ContinuousAt W t := hWc.continuousAt (isOpen_ne.mem_nhds ht.ne')
    have hW2 : ContinuousAt (fun t : ℝ => W (-t)) t :=
      ContinuousAt.comp (hWc.continuousAt (isOpen_ne.mem_nhds (neg_ne_zero.mpr ht.ne'))) continuous_neg.continuousAt
    have hden : ContinuousAt (fun t : ℝ => (t : ℂ)) t := continuous_ofReal.continuousAt
    exact ((hW1.add (hW2.const_mul _)).div hden (ofReal_ne_zero.mpr ht.ne'))
  have hinvF := mellinInv_mellin_eq σ F ht hFconv hFvert hFcont

  have hGconv : MellinConvergent (G p q) σ := by
    apply mellinConvergent_of_mellin_ne_zero
    have h1 : 0 < ((σ : ℂ) + (u₁ + signShift (a₁ + b))).re := by simpa [hp] using hσp
    have h2 : 0 < ((σ : ℂ) + (u₂ + signShift (a₂ + b))).re := by simpa [hq] using hσq
    rw [hp, hq, mellin_G u₁ u₂ a₁ a₂ b _ h1 h2]
    exact archFactor_ne_zero u₁ u₂ a₁ a₂ b _ h1 h2
  have hGvert : VerticalIntegrable (mellin (G p q)) σ := by
    have hI := verticalIntegrable_archFactor u₁ u₂ a₁ a₂ b σ hσp hσq
    refine (integrable_congr (ae_of_all _ fun y => ?_)).mpr hI
    rw [← hFG y]
    exact (hs₀ _ (hline y).1).2
  have hinvG := mellinInv_mellin_eq σ (G p q) ht hGconv hGvert (continuousAt_G p q ht)

  have key : F t = G p q t := by
    rw [← hinvF, ← hinvG]
    exact mellinInv_congr σ hFG t
  have ht' : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  have := congrArg (fun z : ℂ => (t : ℂ) * z) key
  simp only [hF, mul_div_cancel₀ _ ht'] at this
  exact this

end K9sheet

theorem solution
    (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2) (W : ℝ → ℂ)
    (hWc : ContinuousOn W {t : ℝ | t ≠ 0}) (b : ZMod 2)
    (hMel : ∃ s₀ : ℝ, ∀ s : ℂ, s₀ < s.re →
      MellinConvergent (fun t : ℝ => (W t + (-1 : ℂ) ^ b.val * W (-t)) / (t : ℂ)) s ∧
        mellin (fun t : ℝ => (W t + (-1 : ℂ) ^ b.val * W (-t)) / (t : ℂ)) s
          = ((RealArchParam.principal u₁ a₁ u₂ a₂).twist 0 b).archFactor s)
    (t : ℝ) (ht : 0 < t) :
    W t + (-1 : ℂ) ^ b.val * W (-t) =
      (t : ℂ) * ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
        ((r : ℂ) ^ (u₁ + signShift (a₁ + b)) * (Real.exp (-(π * r ^ 2)) : ℂ)) *
          (((t / r : ℝ) : ℂ) ^ (u₂ + signShift (a₂ + b)) * (Real.exp (-(π * (t / r) ^ 2)) : ℂ)) / (r : ℂ)) :=
  K9sheet.main u₁ u₂ a₁ a₂ W hWc b hMel t ht

end S_LanglandsTunnell_add_pow_mul_apply_neg_eq_mul_mulConvGaussian_of_mellin_sheet_eq_archFactor
end P2MW
export P2MW.S_LanglandsTunnell_add_pow_mul_apply_neg_eq_mul_mulConvGaussian_of_mellin_sheet_eq_archFactor (solution)
