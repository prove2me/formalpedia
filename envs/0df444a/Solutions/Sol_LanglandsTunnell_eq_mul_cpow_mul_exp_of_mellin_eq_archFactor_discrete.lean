-- Prove2me | solution 1 for LanglandsTunnell.eq_mul_cpow_mul_exp_of_mellin_eq_archFactor_discrete
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/d60ee3ee-b1b4-5ffc-94f2-f9580e617212

import Definitions.Def_LanglandsTunnell_ArchParam
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.MellinInversion

import Theorems.Thm_Complex_exists_forall_norm_Gamma_le_mul_exp_and_exp_le_mul_norm_Gamma_of_re_mem_Icc_of_one_le_abs_im
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_eq_mul_cpow_mul_exp_of_mellin_eq_archFactor_discrete

set_option autoImplicit false

open scoped Real
open LanglandsTunnell

namespace WPdisc

open Complex MeasureTheory Set Filter Real

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

theorem norm_Gammaℂ_vertical_le {z : ℂ} (hz : 0 < z.re) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y : ℝ, ‖Gammaℂ (z + (y : ℂ) * I)‖ ≤ K * Real.exp (-(π / 4) * |y|) := by
  obtain ⟨K, hK0, hK⟩ := norm_Gamma_vertical_le hz
  refine ⟨2 * (2 * π) ^ (-z.re) * K * Real.exp ((π / 4) * |z.im|), by positivity, fun y => ?_⟩
  rw [Gammaℂ_def, norm_mul, norm_mul]
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  have hπ : ‖(2 * (π : ℂ)) ^ (-(z + (y : ℂ) * I))‖ = (2 * π) ^ (-z.re) := by
    rw [show (2 * (π : ℂ)) = ((2 * π : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : (0 : ℝ) < 2 * π)]
    congr 1
    simp
  have harg : z + (y : ℂ) * I = ((z.re : ℝ) : ℂ) + (((z.im + y) : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp
  rw [h2, hπ, harg]
  have hexp : Real.exp (-(π / 4) * |z.im + y|) ≤ Real.exp ((π / 4) * |z.im|) * Real.exp (-(π / 4) * |y|) := by
    rw [← Real.exp_add, Real.exp_le_exp]
    have : |y| ≤ |z.im + y| + |z.im| := by
      calc |y| = |(z.im + y) - z.im| := by ring_nf
        _ ≤ |z.im + y| + |z.im| := abs_sub _ _
    nlinarith [Real.pi_pos, this]
  calc 2 * (2 * π) ^ (-z.re) * ‖Complex.Gamma (((z.re : ℝ) : ℂ) + (((z.im + y) : ℝ) : ℂ) * I)‖
      ≤ 2 * (2 * π) ^ (-z.re) * (K * Real.exp (-(π / 4) * |z.im + y|)) := by gcongr; exact hK _
    _ ≤ 2 * (2 * π) ^ (-z.re) * (K * (Real.exp ((π / 4) * |z.im|) * Real.exp (-(π / 4) * |y|))) := by gcongr
    _ = _ := by ring

theorem continuous_Gammaℂ_vertical {z : ℂ} (hz : 0 < z.re) :
    Continuous fun y : ℝ => Gammaℂ (z + (y : ℂ) * I) := by
  have hline : Continuous fun y : ℝ => z + (y : ℂ) * I := by fun_prop
  refine continuous_iff_continuousAt.mpr fun y => ?_
  have h1 : ContinuousAt (fun s : ℂ => (2 * (π : ℂ)) ^ (-s)) (z + (y : ℂ) * I) :=
    ContinuousAt.const_cpow (by fun_prop : Continuous fun s : ℂ => -s).continuousAt
      (Or.inl (mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)))
  have h2 : ContinuousAt Complex.Gamma (z + (y : ℂ) * I) := by
    have hne : ∀ m : ℕ, z + (y : ℂ) * I ≠ -(m : ℂ) := by
      intro m h
      have := congrArg Complex.re h
      simp at this
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    exact (Complex.differentiableAt_Gamma _ hne).continuousAt
  have hG : ContinuousAt Gammaℂ (z + (y : ℂ) * I) := by
    have : Gammaℂ = fun s => 2 * (2 * (π : ℂ)) ^ (-s) * Complex.Gamma s := funext Gammaℂ_def
    rw [this]
    exact (continuousAt_const.mul h1).mul h2
  exact ContinuousAt.comp (g := Gammaℂ) (f := fun y : ℝ => z + (y : ℂ) * I) hG hline.continuousAt

theorem integrable_Gammaℂ_vertical {z : ℂ} (hz : 0 < z.re) :
    Integrable fun y : ℝ => Gammaℂ (z + (y : ℂ) * I) := by
  obtain ⟨K, hK0, hK⟩ := norm_Gammaℂ_vertical_le hz
  refine Integrable.mono' ((integrable_exp_neg_mul_abs (by positivity : (0 : ℝ) < π / 4)).const_mul K)
    (continuous_Gammaℂ_vertical hz).aestronglyMeasurable (ae_of_all _ fun y => ?_)
  exact hK y

theorem Gammaℂ_ne_zero_of_re_pos {s : ℂ} (hs : 0 < s.re) : Gammaℂ s ≠ 0 := by
  rw [← Gammaℝ_mul_Gammaℝ_add_one]
  exact mul_ne_zero (Gammaℝ_ne_zero_of_re_pos hs) (Gammaℝ_ne_zero_of_re_pos (by simp; linarith))

theorem archFactor_discrete (u : ℂ) (n : ℕ) (hn : 1 ≤ n) (s : ℂ) :
    (RealArchParam.discrete u n hn).archFactor s = Gammaℂ (s + (u + (n : ℂ) / 2)) := by
  simp [RealArchParam.archFactor, RealArchParam.gammaR, RealArchParam.gammaC]

noncomputable def F₂ (u : ℂ) (n : ℕ) (t : ℝ) : ℂ :=
  ((2 : ℂ) * (t : ℂ) ^ (u + (n : ℂ) / 2 + 1) * (Real.exp (-(2 * π * t)) : ℂ)) / (t : ℂ)

theorem mellin_F₂ (u : ℂ) (n : ℕ) (s : ℂ) (h : 0 < (s + (u + (n : ℂ) / 2)).re) :
    mellin (F₂ u n) s = Gammaℂ (s + (u + (n : ℂ) / 2)) := by
  unfold mellin F₂
  have hpt : ∀ t ∈ Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) • (((2 : ℂ) * (t : ℂ) ^ (u + (n : ℂ) / 2 + 1) *
      (Real.exp (-(2 * π * t)) : ℂ)) / (t : ℂ)) =
      (2 : ℂ) * ((t : ℂ) ^ ((s + (u + (n : ℂ) / 2)) - 1) * Complex.exp (-(((2 * π : ℝ) : ℂ) * (t : ℂ)))) := by
    intro t ht
    have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.2 (ne_of_gt ht)
    have epow : (t : ℂ) ^ (s - 1) * (t : ℂ) ^ (u + (n : ℂ) / 2 + 1) * (t : ℂ)⁻¹ =
        (t : ℂ) ^ ((s + (u + (n : ℂ) / 2)) - 1) := by
      rw [← cpow_neg_one, ← cpow_add _ _ ht0, ← cpow_add _ _ ht0]
      congr 1
      ring
    have eexp : ((Real.exp (-(2 * π * t)) : ℝ) : ℂ) = Complex.exp (-(((2 * π : ℝ) : ℂ) * (t : ℂ))) := by
      rw [Complex.ofReal_exp]; push_cast; ring_nf
    rw [smul_eq_mul, eexp, div_eq_mul_inv]
    linear_combination (2 * Complex.exp (-(((2 * π : ℝ) : ℂ) * (t : ℂ)))) * epow
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul,
    Complex.integral_cpow_mul_exp_neg_mul_Ioi h (by positivity : (0 : ℝ) < 2 * π), Gammaℂ_def]
  have harg : (((2 * π : ℝ) : ℂ)).arg ≠ π := by
    rw [Complex.arg_ofReal_of_nonneg (by positivity)]; exact Real.pi_ne_zero.symm
  rw [one_div, Complex.inv_cpow _ _ harg, ← Complex.cpow_neg]
  push_cast
  ring

theorem continuousAt_F₂ (u : ℂ) (n : ℕ) {t : ℝ} (ht : 0 < t) : ContinuousAt (F₂ u n) t := by
  unfold F₂
  have h1 : ContinuousAt (fun x : ℝ => (x : ℂ) ^ (u + (n : ℂ) / 2 + 1)) t :=
    Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr ht.ne')
  have h2 : ContinuousAt (fun x : ℝ => ((Real.exp (-(2 * π * x)) : ℝ) : ℂ)) t :=
    (Complex.continuous_ofReal.comp (by fun_prop)).continuousAt
  have h3 : ContinuousAt (fun x : ℝ => (x : ℂ)) t := Complex.continuous_ofReal.continuousAt
  exact ((continuousAt_const.mul h1).mul h2).div h3 (ofReal_ne_zero.mpr ht.ne')

theorem main (u : ℂ) (n : ℕ) (hn : 1 ≤ n) (W : ℝ → ℂ)
    (hWc : ContinuousOn W {t : ℝ | t ≠ 0})
    (hMel : ∃ s₀ : ℝ, ∀ s : ℂ, s₀ < s.re →
      MellinConvergent (fun t : ℝ => W t / (t : ℂ)) s ∧
        mellin (fun t : ℝ => W t / (t : ℂ)) s = (RealArchParam.discrete u n hn).archFactor s)
    (t : ℝ) (ht : 0 < t) :
    W t / (t : ℂ) = F₂ u n t := by
  obtain ⟨s₀, hs₀⟩ := hMel
  set p : ℂ := u + (n : ℂ) / 2 with hp
  set F : ℝ → ℂ := fun t : ℝ => W t / (t : ℂ) with hF
  set σ : ℝ := max (s₀ + 1) (1 - p.re) with hσ
  have hσ₀ : s₀ < σ := lt_of_lt_of_le (lt_add_one s₀) (le_max_left _ _)
  have hσp : 0 < σ + p.re := by
    have : 1 - p.re ≤ σ := le_max_right _ _
    linarith
  have hline : ∀ y : ℝ, s₀ < ((σ : ℂ) + (y : ℂ) * I).re ∧ 0 < (((σ : ℂ) + (y : ℂ) * I) + p).re := by
    intro y
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, mul_one, sub_zero, add_zero]
    exact ⟨by simpa using hσ₀, by linarith⟩
  have hFG : ∀ y : ℝ, mellin F ((σ : ℂ) + (y : ℂ) * I) = mellin (F₂ u n) ((σ : ℂ) + (y : ℂ) * I) := by
    intro y
    obtain ⟨h0, h1⟩ := hline y
    rw [(hs₀ _ h0).2, archFactor_discrete, mellin_F₂ u n _ h1]
  have hz : 0 < ((σ : ℂ) + p).re := by simpa using hσp
  have hvert : Integrable fun y : ℝ => Gammaℂ (((σ : ℂ) + p) + (y : ℂ) * I) := integrable_Gammaℂ_vertical hz
  have hvert' : Integrable fun y : ℝ => Gammaℂ (((σ : ℂ) + (y : ℂ) * I) + (u + (n : ℂ) / 2)) := by
    refine (integrable_congr (ae_of_all _ fun y => ?_)).mp hvert
    show Gammaℂ (((σ : ℂ) + p) + (y : ℂ) * I) = Gammaℂ (((σ : ℂ) + (y : ℂ) * I) + (u + (n : ℂ) / 2))
    rw [hp]; ring_nf

  have hσre : s₀ < ((σ : ℂ)).re := by simpa using hσ₀
  have hFconv : MellinConvergent F σ := (hs₀ (σ : ℂ) hσre).1
  have hFvert : VerticalIntegrable (mellin F) σ := by
    refine (integrable_congr (ae_of_all _ fun y => ?_)).mpr hvert'
    rw [(hs₀ _ (hline y).1).2, archFactor_discrete]
  have hFcont : ContinuousAt F t := by
    have hW1 : ContinuousAt W t := hWc.continuousAt (isOpen_ne.mem_nhds ht.ne')
    have hden : ContinuousAt (fun t : ℝ => (t : ℂ)) t := continuous_ofReal.continuousAt
    exact hW1.div hden (ofReal_ne_zero.mpr ht.ne')
  have hinvF := mellinInv_mellin_eq σ F ht hFconv hFvert hFcont

  have hσp' : 0 < ((σ : ℂ) + (u + (n : ℂ) / 2)).re := by simpa [hp] using hσp
  have hGconv : MellinConvergent (F₂ u n) σ := by
    apply mellinConvergent_of_mellin_ne_zero
    rw [mellin_F₂ u n _ hσp']
    exact Gammaℂ_ne_zero_of_re_pos hσp'
  have hGvert : VerticalIntegrable (mellin (F₂ u n)) σ := by
    refine (integrable_congr (ae_of_all _ fun y => ?_)).mpr hvert'
    rw [mellin_F₂ u n _ (hline y).2]
  have hinvG := mellinInv_mellin_eq σ (F₂ u n) ht hGconv hGvert (continuousAt_F₂ u n ht)
  show F t = F₂ u n t
  rw [← hinvF, ← hinvG]
  exact mellinInv_congr σ hFG t

end WPdisc

theorem solution
    (u : ℂ) (n : ℕ) (hn : 1 ≤ n) (W : ℝ → ℂ)
    (hWc : ContinuousOn W {t : ℝ | t ≠ 0})
    (hneg : ∀ t : ℝ, t < 0 → W t = 0)
    (hMel : ∃ s₀ : ℝ, ∀ s : ℂ, s₀ < s.re →
      MellinConvergent (fun t : ℝ => W t / (t : ℂ)) s ∧
        mellin (fun t : ℝ => W t / (t : ℂ)) s = (RealArchParam.discrete u n hn).archFactor s)
    (t : ℝ) (ht : 0 < t) :
    W t = (2 : ℂ) * (t : ℂ) ^ (u + (n : ℂ) / 2 + 1) * (Real.exp (-(2 * π * t)) : ℂ) := by
  have key := WPdisc.main u n hn W hWc hMel t ht
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  unfold WPdisc.F₂ at key
  rw [div_left_inj' ht'] at key
  rw [key]

end S_LanglandsTunnell_eq_mul_cpow_mul_exp_of_mellin_eq_archFactor_discrete
end P2MW
export P2MW.S_LanglandsTunnell_eq_mul_cpow_mul_exp_of_mellin_eq_archFactor_discrete (solution)
