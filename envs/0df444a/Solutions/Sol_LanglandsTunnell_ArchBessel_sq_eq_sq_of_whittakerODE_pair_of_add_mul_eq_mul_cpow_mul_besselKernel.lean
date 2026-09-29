-- Prove2me | solution 1 for LanglandsTunnell.ArchBessel.sq_eq_sq_of_whittakerODE_pair_of_add_mul_eq_mul_cpow_mul_besselKernel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/dc47aea0-3489-57c7-9f2c-2cab4c29fd52

import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Definitions.Def_LanglandsTunnell_ArchBessel
import Theorems.Thm_LanglandsTunnell_ArchBessel_hasDerivAt_besselKernel_and_hasDerivAt_deriv_besselKernel
import Theorems.Thm_LanglandsTunnell_ArchBessel_exists_besselKernel_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_ArchBessel_sq_eq_sq_of_whittakerODE_pair_of_add_mul_eq_mul_cpow_mul_besselKernel

set_option autoImplicit false

namespace EvenElimAux

open Filter Topology

theorem hid (y : ℝ) : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 y := by
  simpa using (hasDerivAt_id y).ofReal_comp

theorem deriv_eq_of_eqOn {f g : ℝ → ℂ} {g' : ℂ} {y : ℝ} (hy : 0 < y)
    (hfg : ∀ y : ℝ, 0 < y → f y = g y) (hg : HasDerivAt g g' y) : deriv f y = g' := by
  have h : f =ᶠ[𝓝 y] g :=
    Filter.eventuallyEq_of_mem (Ioi_mem_nhds hy) fun y' hy' => hfg y' hy'
  rw [h.deriv_eq, hg.deriv]

theorem exists_three_points {K Kp : ℝ → ℂ} (hK : ∀ y : ℝ, 0 < y → HasDerivAt K (Kp y) y)
    {y₀ : ℝ} (hy₀ : 0 < y₀) (hK₀ : K y₀ ≠ 0) :
    ∃ y₁ y₂ : ℝ, 0 < y₁ ∧ 0 < y₂ ∧ y₀ < y₁ ∧ y₁ < y₂ ∧ K y₁ ≠ 0 ∧ K y₂ ≠ 0 := by
  have hc : ContinuousAt K y₀ := (hK y₀ hy₀).continuousAt
  have hev : ∀ᶠ y in 𝓝 y₀, K y ≠ 0 := hc.eventually_ne hK₀
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨y₀ + ε / 4, y₀ + ε / 2, by linarith, by linarith, by linarith, by linarith, hball ?_, hball ?_⟩
  · rw [Real.dist_eq, show y₀ + ε / 4 - y₀ = ε / 4 by ring, abs_of_pos (by linarith)]; linarith
  · rw [Real.dist_eq, show y₀ + ε / 2 - y₀ = ε / 2 by ring, abs_of_pos (by linarith)]; linarith

theorem coeffs_eq_zero (c₄ c₂ c₀ : ℂ) (t₀ t₁ t₂ : ℂ) (h01 : t₀ ≠ t₁) (h02 : t₀ ≠ t₂) (h12 : t₁ ≠ t₂)
    (e0 : c₄ * t₀ ^ 2 + c₂ * t₀ + c₀ = 0) (e1 : c₄ * t₁ ^ 2 + c₂ * t₁ + c₀ = 0)
    (e2 : c₄ * t₂ ^ 2 + c₂ * t₂ + c₀ = 0) : c₄ = 0 ∧ c₂ = 0 ∧ c₀ = 0 := by
  have f01 : (t₀ - t₁) * (c₄ * (t₀ + t₁) + c₂) = 0 := by linear_combination e0 - e1
  have f02 : (t₀ - t₂) * (c₄ * (t₀ + t₂) + c₂) = 0 := by linear_combination e0 - e2
  have g01 := (mul_eq_zero.mp f01).resolve_left (sub_ne_zero.mpr h01)
  have g02 := (mul_eq_zero.mp f02).resolve_left (sub_ne_zero.mpr h02)
  have hc4 : c₄ = 0 := by
    have : c₄ * (t₁ - t₂) = 0 := by linear_combination g01 - g02
    exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr h12)
  have hc2 : c₂ = 0 := by linear_combination g01 - (t₀ + t₁) * hc4
  refine ⟨hc4, hc2, ?_⟩
  linear_combination e0 - t₀ ^ 2 * hc4 - t₀ * hc2

theorem riccati (A μ p₂ p₀ q₁ : ℂ) (K Kp : ℝ → ℂ) (hA : A ≠ 0)
    (hK : ∀ y : ℝ, 0 < y → HasDerivAt K (Kp y) y)
    (hKp : ∀ y : ℝ, 0 < y → HasDerivAt Kp (A * K y + μ ^ 2 / (y : ℂ) ^ 2 * K y - Kp y / (y : ℂ)) y)
    (hne : ∃ y₀ : ℝ, 0 < y₀ ∧ K y₀ ≠ 0)
    (hZ : ∀ y : ℝ, 0 < y → (p₂ * (y : ℂ) ^ 2 + p₀) * K y + q₁ * (y : ℂ) * Kp y = 0) :
    p₂ = 0 ∧ p₀ = 0 ∧ q₁ = 0 := by

  have hR : ∀ y : ℝ, 0 < y →
      (-p₂ ^ 2 * ((y : ℂ) ^ 2) ^ 2 + (A * q₁ ^ 2 - 2 * p₀ * p₂ + 2 * p₂ * q₁) * (y : ℂ) ^ 2
        + (q₁ ^ 2 * μ ^ 2 - p₀ ^ 2)) * K y = 0 := by
    intro y hy
    have hy0 : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
    have hd := ((((((hid y).pow 2).const_mul p₂).add_const p₀).mul (hK y hy)).add
      (((hid y).const_mul q₁).mul (hKp y hy)))
    have hzero : deriv (fun y : ℝ => (p₂ * (y : ℂ) ^ 2 + p₀) * K y + q₁ * (y : ℂ) * Kp y) y = 0 :=
      deriv_eq_of_eqOn (g := fun _ => (0 : ℂ)) hy hZ (hasDerivAt_const y 0)
    have hraw : deriv (fun y : ℝ => (p₂ * (y : ℂ) ^ 2 + p₀) * K y + q₁ * (y : ℂ) * Kp y) y = _ := hd.deriv
    rw [hzero] at hraw
    simp only [Pi.pow_apply] at hraw

    have h1 := hZ y hy
    linear_combination (norm := skip) (-(q₁ * (y : ℂ))) * hraw - (p₂ * (y:ℂ) ^ 2 + p₀ + q₁ - q₁) * h1
    field_simp
    ring
  obtain ⟨y₀, hy₀, hK₀⟩ := hne
  obtain ⟨y₁, y₂, hy₁, hy₂, h01, h12, hK₁, hK₂⟩ := exists_three_points hK hy₀ hK₀
  have e0 := (mul_eq_zero.mp (hR y₀ hy₀)).resolve_right hK₀
  have e1 := (mul_eq_zero.mp (hR y₁ hy₁)).resolve_right hK₁
  have e2 := (mul_eq_zero.mp (hR y₂ hy₂)).resolve_right hK₂
  have hsq : ∀ {s t : ℝ}, 0 < s → 0 < t → s < t → ((s : ℂ)) ^ 2 ≠ ((t : ℂ)) ^ 2 := by
    intro s t hs ht hst h
    norm_cast at h
    have := (sq_eq_sq₀ hs.le ht.le).mp h
    linarith
  obtain ⟨hc4, hc2, hc0⟩ := coeffs_eq_zero (-p₂ ^ 2) (A * q₁ ^ 2 - 2 * p₀ * p₂ + 2 * p₂ * q₁) (q₁ ^ 2 * μ ^ 2 - p₀ ^ 2)
    (((y₀ : ℂ)) ^ 2) (((y₁ : ℂ)) ^ 2) (((y₂ : ℂ)) ^ 2) (hsq hy₀ hy₁ h01) (hsq hy₀ hy₂ (h01.trans h12)) (hsq hy₁ hy₂ h12)
    e0 e1 e2
  have hp₂ : p₂ = 0 := pow_eq_zero_iff two_ne_zero |>.mp (neg_eq_zero.mp hc4)
  have hq₁ : q₁ = 0 := by
    rw [hp₂] at hc2
    have : A * q₁ ^ 2 = 0 := by linear_combination hc2
    exact pow_eq_zero_iff two_ne_zero |>.mp ((mul_eq_zero.mp this).resolve_left hA)
  have hp₀ : p₀ = 0 := by
    rw [hq₁] at hc0
    have : p₀ ^ 2 = 0 := by linear_combination -hc0
    exact pow_eq_zero_iff two_ne_zero |>.mp this
  exact ⟨hp₂, hp₀, hq₁⟩

end EvenElimAux

open LanglandsTunnell.ArchBessel EvenElimAux Filter Topology in
theorem solution
    (ν μ c ε C a : ℂ) (P Q : ℝ → ℂ)
    (hP : DifferentiableOn ℝ P (Set.Ioi 0)) (hP' : DifferentiableOn ℝ (deriv P) (Set.Ioi 0))
    (hPode : ∀ y : ℝ, 0 < y →
      (y : ℂ) ^ 2 * deriv (deriv P) y
        + (1 / 4 - ν ^ 2 + 2 * (Real.pi : ℂ) * c * (y : ℂ) - 4 * (Real.pi : ℂ) ^ 2 * (y : ℂ) ^ 2) * P y = 0)
    (hQ : DifferentiableOn ℝ Q (Set.Ioi 0)) (hQ' : DifferentiableOn ℝ (deriv Q) (Set.Ioi 0))
    (hQode : ∀ y : ℝ, 0 < y →
      (y : ℂ) ^ 2 * deriv (deriv Q) y
        + (1 / 4 - ν ^ 2 - 2 * (Real.pi : ℂ) * c * (y : ℂ) - 4 * (Real.pi : ℂ) ^ 2 * (y : ℂ) ^ 2) * Q y = 0)
    (hC : C ≠ 0) (ha : a = 1 / 2 ∨ a = 3 / 2)
    (hH : ∀ y : ℝ, 0 < y → P y + ε * Q y = C * (y : ℂ) ^ a * besselKernel μ (2 * Real.pi * y)) :
    μ ^ 2 = ν ^ 2 := by

  set K : ℝ → ℂ := fun y => besselKernel μ (2 * Real.pi * y) with hKdef
  set Kp : ℝ → ℂ := fun y => (2 * Real.pi : ℂ) *
      (-besselKernel (μ + 1) (2 * Real.pi * y) + μ / ((2 * Real.pi * y : ℝ) : ℂ) * besselKernel μ (2 * Real.pi * y)) with hKpdef
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hsc : ∀ y : ℝ, HasDerivAt (fun y : ℝ => 2 * Real.pi * y) (2 * Real.pi) y := fun y => by
    simpa using (hasDerivAt_id y).const_mul (2 * Real.pi)
  have hK : ∀ y : ℝ, 0 < y → HasDerivAt K (Kp y) y := by
    intro y hy
    have hx : 0 < 2 * Real.pi * y := by positivity
    have h1 := (LanglandsTunnell.ArchBessel.hasDerivAt_besselKernel_and_hasDerivAt_deriv_besselKernel μ _ hx).1
    have h := h1.scomp y (hsc y)
    convert h using 1
    all_goals first | rfl | skip
    rw [hKpdef, Complex.real_smul]
    push_cast
    ring
  have hderiv : ∀ y : ℝ, 0 < y →
      deriv (fun x : ℝ => besselKernel μ x) (2 * Real.pi * y) = Kp y / (2 * Real.pi : ℂ) := by
    intro y hy
    have hx : 0 < 2 * Real.pi * y := by positivity
    rw [(LanglandsTunnell.ArchBessel.hasDerivAt_besselKernel_and_hasDerivAt_deriv_besselKernel μ _ hx).1.deriv,
      hKpdef]
    field_simp
  set A : ℂ := 4 * (Real.pi : ℂ) ^ 2 with hAdef
  have hA : A ≠ 0 := by rw [hAdef]; exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hπ)
  have hKp : ∀ y : ℝ, 0 < y → HasDerivAt Kp
      (A * K y + μ ^ 2 / (y : ℂ) ^ 2 * K y - Kp y / (y : ℂ)) y := by
    intro y hy
    have hx : 0 < 2 * Real.pi * y := by positivity
    have hy0 : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
    have h2 := (LanglandsTunnell.ArchBessel.hasDerivAt_besselKernel_and_hasDerivAt_deriv_besselKernel μ _ hx).2
    have h := (h2.scomp y (hsc y)).const_mul (2 * Real.pi : ℂ)
    have heq : Kp =ᶠ[𝓝 y] fun y : ℝ => (2 * Real.pi : ℂ) * deriv (fun x : ℝ => besselKernel μ x) (2 * Real.pi * y) := by
      refine Filter.eventuallyEq_of_mem (Ioi_mem_nhds hy) fun y' hy' => ?_
      show Kp y' = (2 * Real.pi : ℂ) * deriv (fun x : ℝ => besselKernel μ x) (2 * Real.pi * y')
      rw [hderiv y' hy']
      field_simp
    refine (h.congr_of_eventuallyEq heq).congr_deriv ?_
    rw [hderiv y hy, Complex.real_smul, hKdef, hAdef]
    push_cast
    field_simp
    ring
  have hne : ∃ y₀ : ℝ, 0 < y₀ ∧ K y₀ ≠ 0 := by
    obtain ⟨x, hx, hx0⟩ := LanglandsTunnell.ArchBessel.exists_besselKernel_ne_zero μ
    refine ⟨x / (2 * Real.pi), by positivity, ?_⟩
    rw [hKdef]
    show besselKernel μ (2 * Real.pi * (x / (2 * Real.pi))) ≠ 0
    rwa [mul_div_cancel₀ x (by positivity : (2 * Real.pi : ℝ) ≠ 0)]

  set T : ℝ → ℂ := fun y => C * (y : ℂ) ^ a with hTdef
  have hT : ∀ y : ℝ, 0 < y → HasDerivAt T (a * T y / (y : ℂ)) y := by
    intro y hy
    have hy0 : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
    have hsl : 0 < ((y : ℝ) : ℂ).re ∨ ((y : ℝ) : ℂ).im ≠ 0 := Or.inl (by simpa using hy)
    have h := ((Complex.hasStrictDerivAt_cpow_const (c := a) hsl).hasDerivAt.comp_ofReal).const_mul C
    convert h using 1
    all_goals first | rfl | skip
    rw [hTdef, Complex.cpow_sub _ _ hy0, Complex.cpow_one]
    field_simp
  have hT0 : ∀ y : ℝ, 0 < y → T y ≠ 0 := by
    intro y hy
    have hy0 : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
    rw [hTdef]
    exact mul_ne_zero hC (fun h => hy0 (Complex.cpow_eq_zero_iff _ _ |>.mp h).1)

  have hHf : ∀ y : ℝ, 0 < y → P y + ε * Q y = T y * K y := by
    exact fun y hy => hH y hy

  have hdH : ∀ y : ℝ, 0 < y → deriv (fun y => P y + ε * Q y) y = deriv P y + ε * deriv Q y := by
    intro y hy
    exact (((hP.differentiableAt (Ioi_mem_nhds hy)).hasDerivAt).add
      ((hQ.differentiableAt (Ioi_mem_nhds hy)).hasDerivAt.const_mul ε)).deriv
  have hddH : ∀ y : ℝ, 0 < y →
      deriv (deriv (fun y => P y + ε * Q y)) y = deriv (deriv P) y + ε * deriv (deriv Q) y := by
    intro y hy
    exact deriv_eq_of_eqOn hy hdH (((hP'.differentiableAt (Ioi_mem_nhds hy)).hasDerivAt).add
      ((hQ'.differentiableAt (Ioi_mem_nhds hy)).hasDerivAt.const_mul ε))
  have hdG : ∀ y : ℝ, 0 < y → deriv (fun y => P y - ε * Q y) y = deriv P y - ε * deriv Q y := by
    intro y hy
    exact (((hP.differentiableAt (Ioi_mem_nhds hy)).hasDerivAt).sub
      ((hQ.differentiableAt (Ioi_mem_nhds hy)).hasDerivAt.const_mul ε)).deriv
  have hddG : ∀ y : ℝ, 0 < y →
      deriv (deriv (fun y => P y - ε * Q y)) y = deriv (deriv P) y - ε * deriv (deriv Q) y := by
    intro y hy
    exact deriv_eq_of_eqOn hy hdG (((hP'.differentiableAt (Ioi_mem_nhds hy)).hasDerivAt).sub
      ((hQ'.differentiableAt (Ioi_mem_nhds hy)).hasDerivAt.const_mul ε))

  set H1 : ℝ → ℂ := fun y => T y * (a * K y / (y : ℂ) + Kp y) with hH1
  have hdTK : ∀ y : ℝ, 0 < y → HasDerivAt (fun y => P y + ε * Q y) (H1 y) y := by
    intro y hy
    have hy0 : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
    have h := (hT y hy).mul (hK y hy)
    have h' : HasDerivAt (fun y => T y * K y) (H1 y) y := by
      convert h using 1
      all_goals first | rfl | skip
      rw [hH1]
      beta_reduce
      field_simp
    exact h'.congr_of_eventuallyEq (Filter.eventuallyEq_of_mem (Ioi_mem_nhds hy) fun y' hy' => hHf y' hy')
  have hdH1 : ∀ y : ℝ, 0 < y → deriv (fun y => P y + ε * Q y) y = H1 y := fun y hy => (hdTK y hy).deriv
  set H2 : ℝ → ℂ := fun y => T y * (A * K y + (a ^ 2 - a + μ ^ 2) * K y / (y : ℂ) ^ 2 + (2 * a - 1) * Kp y / (y : ℂ))
    with hH2
  have hH2v : ∀ y : ℝ, 0 < y → deriv (deriv (fun y => P y + ε * Q y)) y = H2 y := by
    intro y hy
    have hy0 : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
    have h := (hT y hy).mul (((((hK y hy).const_mul a).div (hid y) hy0)).add (hKp y hy))
    have h' : HasDerivAt H1 (H2 y) y := by
      convert h using 1
      all_goals first | rfl | skip
      rw [hH2]
      beta_reduce
      try simp only [Pi.div_apply, Pi.add_apply, Pi.mul_apply, Pi.pow_apply, Pi.sub_apply]
      field_simp
      ring
    exact deriv_eq_of_eqOn hy hdH1 h'

  have eq1 : ∀ y : ℝ, 0 < y →
      (y : ℂ) ^ 2 * H2 y + (1 / 4 - ν ^ 2 - A * (y : ℂ) ^ 2) * (T y * K y)
        + (2 * (Real.pi : ℂ) * c) * (y : ℂ) * (P y - ε * Q y) = 0 := by
    intro y hy
    have e1 := hPode y hy
    have e2 := hQode y hy
    have e3 := hH2v y hy
    rw [hddH y hy] at e3
    have e4 := hHf y hy
    rw [hAdef]
    linear_combination e1 + ε * e2 - (y : ℂ) ^ 2 * e3 - (1 / 4 - ν ^ 2 - 4 * (Real.pi : ℂ) ^ 2 * (y : ℂ) ^ 2) * e4
  by_cases hc : c = 0
  ·
    have hZ : ∀ y : ℝ, 0 < y →
        (0 * (y : ℂ) ^ 2 + ((a - 1 / 2) ^ 2 + (μ ^ 2 - ν ^ 2))) * K y + (2 * a - 1) * (y : ℂ) * Kp y = 0 := by
      intro y hy
      have hy0 : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
      have e := eq1 y hy
      rw [hc, hH2] at e
      beta_reduce at e
      have : T y * ((0 * (y : ℂ) ^ 2 + ((a - 1 / 2) ^ 2 + (μ ^ 2 - ν ^ 2))) * K y + (2 * a - 1) * (y : ℂ) * Kp y) = 0 := by
        linear_combination (norm := skip) e
        field_simp
        ring
      exact (mul_eq_zero.mp this).resolve_left (hT0 y hy)
    obtain ⟨-, hp₀, hq₁⟩ := riccati A μ 0 ((a - 1 / 2) ^ 2 + (μ ^ 2 - ν ^ 2)) (2 * a - 1) K Kp hA hK hKp hne hZ
    have ha' : a = 1 / 2 := by linear_combination hq₁ / 2
    rw [ha'] at hp₀
    linear_combination hp₀
  ·
    set B : ℂ := 2 * (Real.pi : ℂ) * c with hBdef
    have hB : B ≠ 0 := by rw [hBdef]; exact mul_ne_zero (mul_ne_zero two_ne_zero hπ) hc
    set d₀ : ℂ := a ^ 2 - a + μ ^ 2 - ν ^ 2 + 1 / 4 with hd₀
    set Gf : ℝ → ℂ := fun y => T y / B * (-d₀ * K y / (y : ℂ) + (1 - 2 * a) * Kp y) with hGfdef
    have hGf : ∀ y : ℝ, 0 < y → P y - ε * Q y = Gf y := by
      intro y hy
      have hy0 : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
      have e := eq1 y hy
      rw [hH2] at e
      apply mul_left_cancel₀ (mul_ne_zero hB hy0)
      have : B * (y : ℂ) * Gf y
          = -((y : ℂ) ^ 2 * (T y * (A * K y + (a ^ 2 - a + μ ^ 2) * K y / (y : ℂ) ^ 2 + (2 * a - 1) * Kp y / (y : ℂ)))
              + (1 / 4 - ν ^ 2 - A * (y : ℂ) ^ 2) * (T y * K y)) := by
        rw [hGfdef, hd₀]
        beta_reduce
        field_simp
        ring
      rw [this, hBdef]
      linear_combination e
    set G1 : ℝ → ℂ := fun y => T y / B *
        (((-2 * A * a + A) + (-a ^ 3 + 2 * a ^ 2 - 3 * a * μ ^ 2 + a * ν ^ 2 - 5 / 4 * a + 2 * μ ^ 2 - ν ^ 2 + 1 / 4)
            / (y : ℂ) ^ 2) * K y
          + ((-3 * a ^ 2 + 4 * a - μ ^ 2 + ν ^ 2 - 5 / 4) / (y : ℂ)) * Kp y) with hG1def
    have hdGf : ∀ y : ℝ, 0 < y → HasDerivAt Gf (G1 y) y := by
      intro y hy
      have hy0 : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
      have h := ((hT y hy).div_const B).mul
        (((((hK y hy).const_mul (-d₀)).div (hid y) hy0)).add ((hKp y hy).const_mul (1 - 2 * a)))
      convert h using 1
      all_goals first | rfl | skip
      rw [hG1def, hd₀]
      beta_reduce
      try simp only [Pi.div_apply, Pi.add_apply, Pi.mul_apply, Pi.pow_apply, Pi.sub_apply]
      field_simp
      ring
    have hdG1 : ∀ y : ℝ, 0 < y → deriv (fun y => P y - ε * Q y) y = G1 y :=
      fun y hy => deriv_eq_of_eqOn hy hGf (hdGf y hy)

    have hZ : ∀ y : ℝ, 0 < y →
        ((-64 * A * a ^ 2 + 64 * A * a - 16 * A + 16 * B ^ 2) * (y : ℂ) ^ 2
            + (-16 * a ^ 4 + 64 * a ^ 3 - 96 * a ^ 2 * μ ^ 2 + 32 * a ^ 2 * ν ^ 2 - 88 * a ^ 2 + 192 * a * μ ^ 2
                - 64 * a * ν ^ 2 + 48 * a - 16 * μ ^ 4 + 32 * μ ^ 2 * ν ^ 2 - 88 * μ ^ 2 - 16 * ν ^ 4 + 40 * ν ^ 2 - 9)) * K y
          + (-16 * (a - 1) * (4 * a ^ 2 - 8 * a + 4 * μ ^ 2 - 4 * ν ^ 2 + 3)) * (y : ℂ) * Kp y = 0 := by
      intro y hy
      have hy0 : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'

      have u1 := (hasDerivAt_const y (-2 * A * a + A)).add
        ((hasDerivAt_const y (-a ^ 3 + 2 * a ^ 2 - 3 * a * μ ^ 2 + a * ν ^ 2 - 5 / 4 * a + 2 * μ ^ 2 - ν ^ 2 + 1 / 4)).div
          ((hid y).pow 2) (pow_ne_zero 2 hy0))
      have u2 := (hasDerivAt_const y (-3 * a ^ 2 + 4 * a - μ ^ 2 + ν ^ 2 - 5 / 4)).div (hid y) hy0
      have h := ((hT y hy).div_const B).mul ((u1.mul (hK y hy)).add (u2.mul (hKp y hy)))
      have hG2 : deriv (deriv (fun y => P y - ε * Q y)) y = _ := deriv_eq_of_eqOn hy hdG1 h
      have e1 := hPode y hy
      have e2 := hQode y hy
      have e5 := hddG y hy
      have eq2 : (y : ℂ) ^ 2 * deriv (deriv (fun y => P y - ε * Q y)) y
          + (1 / 4 - ν ^ 2 - A * (y : ℂ) ^ 2) * (P y - ε * Q y) + B * (y : ℂ) * (P y + ε * Q y) = 0 := by
        rw [hAdef, hBdef]
        linear_combination e1 - ε * e2 + (y : ℂ) ^ 2 * e5
      rw [hG2, hGf y hy, hHf y hy, hGfdef] at eq2
      beta_reduce at eq2
      try simp only [Pi.div_apply, Pi.add_apply, Pi.mul_apply, Pi.pow_apply, Pi.sub_apply] at eq2
      have hpoly : T y * (((-64 * A * a ^ 2 + 64 * A * a - 16 * A + 16 * B ^ 2) * (y : ℂ) ^ 2
            + (-16 * a ^ 4 + 64 * a ^ 3 - 96 * a ^ 2 * μ ^ 2 + 32 * a ^ 2 * ν ^ 2 - 88 * a ^ 2 + 192 * a * μ ^ 2
                - 64 * a * ν ^ 2 + 48 * a - 16 * μ ^ 4 + 32 * μ ^ 2 * ν ^ 2 - 88 * μ ^ 2 - 16 * ν ^ 4 + 40 * ν ^ 2 - 9)) * K y
          + (-16 * (a - 1) * (4 * a ^ 2 - 8 * a + 4 * μ ^ 2 - 4 * ν ^ 2 + 3)) * (y : ℂ) * Kp y) = 0 := by
        linear_combination (norm := skip) (16 * B * (y : ℂ)) * eq2
        field_simp
        ring
      exact (mul_eq_zero.mp hpoly).resolve_left (hT0 y hy)
    obtain ⟨-, -, hq₁⟩ := riccati A μ _ _ _ K Kp hA hK hKp hne hZ
    have ha1 : a - 1 ≠ 0 := by
      rcases ha with h | h <;> (rw [h]; norm_num)
    have hquad : 4 * a ^ 2 - 8 * a + 3 = 0 := by
      rcases ha with h | h <;> (rw [h]; norm_num)
    have h16 : (-16 : ℂ) * (a - 1) ≠ 0 := mul_ne_zero (by norm_num) ha1
    have := (mul_eq_zero.mp hq₁).resolve_left h16
    linear_combination this / 4 - hquad / 4

end S_LanglandsTunnell_ArchBessel_sq_eq_sq_of_whittakerODE_pair_of_add_mul_eq_mul_cpow_mul_besselKernel
end P2MW
export P2MW.S_LanglandsTunnell_ArchBessel_sq_eq_sq_of_whittakerODE_pair_of_add_mul_eq_mul_cpow_mul_besselKernel (solution)
