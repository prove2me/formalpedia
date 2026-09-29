-- Prove2me | solution 1 for HarmonicOscillator.eq_cos_smul_add_sin_smul
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-28T00:47:56.795832+00:00
-- url     : https://prove2.me/submissions/e0d5c4c6-f51b-490e-b6d4-3df3e3d973a6

import Mathlib

theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g g' g'' : ℝ → E) (alpha : ℝ) (halpha : alpha ≠ 0)
    (hg : ∀ t, HasDerivAt g (g' t) t)
    (hg' : ∀ t, HasDerivAt g' (g'' t) t)
    (heq : ∀ t, g'' t = -(alpha ^ 2) • g t) :
    ∀ t, g t = Real.cos (alpha * t) • g 0 + (Real.sin (alpha * t) / alpha) • g' 0 := by
  set v1 : E := g 0 with hv1
  set v2 : E := (1 / alpha) • g' 0 with hv2
  -- the model solution and its two derivatives
  set G : ℝ → E := fun t => Real.cos (alpha * t) • v1 + Real.sin (alpha * t) • v2 with hG
  set G' : ℝ → E := fun t =>
    (-(alpha * Real.sin (alpha * t))) • v1 + (alpha * Real.cos (alpha * t)) • v2 with hG'
  set G'' : ℝ → E := fun t =>
    (-(alpha ^ 2 * Real.cos (alpha * t))) • v1 + (-(alpha ^ 2 * Real.sin (alpha * t))) • v2
    with hG''
  have hlin : ∀ t : ℝ, HasDerivAt (fun t : ℝ => alpha * t) alpha t := by
    intro t; simpa using (hasDerivAt_id t).const_mul alpha
  have hGd : ∀ t, HasDerivAt G (G' t) t := by
    intro t
    have hc : HasDerivAt (fun t : ℝ => Real.cos (alpha * t)) (-Real.sin (alpha * t) * alpha) t :=
      (Real.hasDerivAt_cos (alpha * t)).comp t (hlin t)
    have hs : HasDerivAt (fun t : ℝ => Real.sin (alpha * t)) (Real.cos (alpha * t) * alpha) t :=
      (Real.hasDerivAt_sin (alpha * t)).comp t (hlin t)
    have := (hc.smul_const v1).add (hs.smul_const v2)
    refine this.congr_deriv ?_
    simp only [hG']
    module
  have hG'd : ∀ t, HasDerivAt G' (G'' t) t := by
    intro t
    have hc : HasDerivAt (fun t : ℝ => Real.cos (alpha * t)) (-Real.sin (alpha * t) * alpha) t :=
      (Real.hasDerivAt_cos (alpha * t)).comp t (hlin t)
    have hs : HasDerivAt (fun t : ℝ => Real.sin (alpha * t)) (Real.cos (alpha * t) * alpha) t :=
      (Real.hasDerivAt_sin (alpha * t)).comp t (hlin t)
    have h1 : HasDerivAt (fun t : ℝ => -(alpha * Real.sin (alpha * t)))
        (-(alpha * (Real.cos (alpha * t) * alpha))) t := (hs.const_mul alpha).neg
    have h2 : HasDerivAt (fun t : ℝ => alpha * Real.cos (alpha * t))
        (alpha * (-Real.sin (alpha * t) * alpha)) t := hc.const_mul alpha
    have := (h1.smul_const v1).add (h2.smul_const v2)
    refine this.congr_deriv ?_
    simp only [hG'']
    module
  have hGeq : ∀ t, G'' t = -(alpha ^ 2) • G t := by
    intro t
    simp only [hG, hG'']
    module
  -- the difference and its energy
  set F : ℝ → E := fun t => g t - G t with hF
  set Fd : ℝ → E := fun t => g' t - G' t with hFd
  have hFdd : ∀ t, HasDerivAt F (Fd t) t := fun t => (hg t).sub (hGd t)
  have hFd2 : ∀ t, HasDerivAt Fd (-(alpha ^ 2) • F t) t := by
    intro t
    have := (hg' t).sub (hG'd t)
    rw [heq t, hGeq t] at this
    refine this.congr_deriv ?_
    simp only [hF]
    module
  set En : ℝ → ℝ := fun t => (inner ℝ (Fd t) (Fd t)) + alpha ^ 2 * (inner ℝ (F t) (F t)) with hEn
  have hEnd : ∀ t, HasDerivAt En 0 t := by
    intro t
    have h1 : HasDerivAt (fun t => (inner ℝ (Fd t) (Fd t) : ℝ))
        ((inner ℝ (Fd t) (-(alpha ^ 2) • F t) : ℝ) + (inner ℝ (-(alpha ^ 2) • F t) (Fd t) : ℝ)) t :=
      HasDerivAt.inner ℝ (hFd2 t) (hFd2 t)
    have h2 : HasDerivAt (fun t => (inner ℝ (F t) (F t) : ℝ))
        ((inner ℝ (F t) (Fd t) : ℝ) + (inner ℝ (Fd t) (F t) : ℝ)) t :=
      HasDerivAt.inner ℝ (hFdd t) (hFdd t)
    have := h1.add (h2.const_mul (alpha ^ 2))
    refine this.congr_deriv ?_
    rw [real_inner_smul_left, real_inner_smul_right, real_inner_comm (F t) (Fd t)]
    ring
  have hEnconst : ∀ t, En t = En 0 := by
    intro t
    exact is_const_of_deriv_eq_zero (fun x => (hEnd x).differentiableAt)
      (fun x => (hEnd x).deriv) t 0
  have hEn0 : En 0 = 0 := by
    have hF0 : F 0 = 0 := by simp [hF, hG, hv1]
    have hFd0 : Fd 0 = 0 := by
      simp only [hFd, hG', hv2, mul_zero, Real.sin_zero, Real.cos_zero, mul_one,
        neg_zero, zero_smul, zero_add, smul_smul]
      rw [mul_one_div, div_self halpha, one_smul, sub_self]
    simp [hEn, hF0, hFd0]
  intro t
  have hzero : F t = 0 := by
    have h := hEnconst t
    rw [hEn0] at h
    have h1 : (0:ℝ) ≤ inner ℝ (Fd t) (Fd t) := real_inner_self_nonneg
    have h2 : (0:ℝ) ≤ inner ℝ (F t) (F t) := real_inner_self_nonneg
    have ha2 : (0:ℝ) < alpha ^ 2 := by positivity
    have : (inner ℝ (F t) (F t) : ℝ) = 0 := by
      simp only [hEn] at h
      nlinarith
    exact inner_self_eq_zero.mp this
  have : g t = G t := by
    have := hzero
    simp only [hF, sub_eq_zero] at this
    exact this
  rw [this]
  simp only [hG, hv1, hv2, smul_smul]
  congr 2
  field_simp
