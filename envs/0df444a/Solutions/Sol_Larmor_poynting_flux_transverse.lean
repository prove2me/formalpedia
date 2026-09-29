-- Prove2me | solution 1 for Larmor.poynting_flux_transverse
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T21:54:48.830113+00:00
-- url     : https://prove2.me/submissions/749bd0b6-4a4a-43c0-b52e-ffd0885b86de

import Definitions.Def_Larmor_radiated_power
import Definitions.Def_Larmor_lienard_wiechert
import Definitions.Def_Larmor_em_fields

open Larmor

theorem W3a_Larmor_inner (a b : Vec) :
    inner ℝ a b = a 0 * b 0 + a 1 * b 1 + a 2 * b 2 := by
  simp [PiLp.inner_apply, Fin.sum_univ_three]
  ring

theorem W3a_Larmor_normsq (a : Vec) : ‖a‖ ^ 2 = a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [Fin.sum_univ_three]

theorem W3a_Larmor_cross0 (u v : Vec) : cross u v 0 = u 1 * v 2 - u 2 * v 1 := by simp [cross]
theorem W3a_Larmor_cross1 (u v : Vec) : cross u v 1 = u 2 * v 0 - u 0 * v 2 := by simp [cross]
theorem W3a_Larmor_cross2 (u v : Vec) : cross u v 2 = u 0 * v 1 - u 1 * v 0 := by simp [cross]

theorem W3a_Larmor_curl0 (F : Vec → Vec) (x : Vec) :
    curl F x 0 = partialDeriv F 1 2 x - partialDeriv F 2 1 x := by simp [curl]
theorem W3a_Larmor_curl1 (F : Vec → Vec) (x : Vec) :
    curl F x 1 = partialDeriv F 2 0 x - partialDeriv F 0 2 x := by simp [curl]
theorem W3a_Larmor_curl2 (F : Vec → Vec) (x : Vec) :
    curl F x 2 = partialDeriv F 0 1 x - partialDeriv F 1 0 x := by simp [curl]

theorem solution (ε₀ c : ℝ) (Ev n : Vec) (hn : ‖n‖ = 1) :
    inner ℝ (poynting ε₀ c Ev (c⁻¹ • cross n Ev)) n
      = ε₀ * c * (‖Ev‖ ^ 2 - (inner ℝ Ev n : ℝ) ^ 2) := by
  have hn2 : n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1 := by
    rw [← W3a_Larmor_normsq, hn]; norm_num
  have hc : c ^ 2 * c⁻¹ = c := by
    rcases eq_or_ne c 0 with h | h
    · simp [h]
    · field_simp
  rw [W3a_Larmor_inner, W3a_Larmor_normsq, W3a_Larmor_inner Ev n]
  simp only [poynting, PiLp.smul_apply, smul_eq_mul, W3a_Larmor_cross0, W3a_Larmor_cross1,
    W3a_Larmor_cross2]
  linear_combination
    ε₀ * ((Ev 0 ^ 2 + Ev 1 ^ 2 + Ev 2 ^ 2) * (n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2)
      - (Ev 0 * n 0 + Ev 1 * n 1 + Ev 2 * n 2) ^ 2) * hc
    + ε₀ * c * (Ev 0 ^ 2 + Ev 1 ^ 2 + Ev 2 ^ 2) * hn2

theorem W3a_Larmor_retarded_time_on_sphere (c R t : ℝ) (hc : 0 < c) (hR : 0 < R)
    (ht : c * t = R) (w : ℝ → Vec) (hw0 : w 0 = 0) (x : Vec) (hx : ‖x‖ = R) :
    IsRetardedTime c w t x 0 := by
  refine ⟨?_, ?_⟩
  · by_contra h
    push_neg at h
    nlinarith
  · rw [hw0, sub_zero, sub_zero, hx, ht]

theorem W3a_Larmor_retarded_time_unique (c : ℝ) (hc : 0 < c) (K : NNReal) (hK : (K : ℝ) < c)
    (w : ℝ → Vec) (hw : LipschitzWith K w) (t : ℝ) (x : Vec) (t₁ t₂ : ℝ)
    (h₁ : IsRetardedTime c w t x t₁) (h₂ : IsRetardedTime c w t x t₂) : t₁ = t₂ := by
  obtain ⟨_, e1⟩ := h₁
  obtain ⟨_, e2⟩ := h₂
  have hL := hw.dist_le_mul t₁ t₂
  rw [dist_eq_norm, Real.dist_eq] at hL
  have h3 := abs_norm_sub_norm_le (x - w t₁) (x - w t₂)
  have e : (x - w t₁) - (x - w t₂) = -(w t₁ - w t₂) := by abel
  rw [e, norm_neg, ← e1, ← e2] at h3
  have h4 : c * (t - t₁) - c * (t - t₂) = c * (t₂ - t₁) := by ring
  rw [h4, abs_mul, abs_of_pos hc, abs_sub_comm] at h3
  have h5 : c * |t₁ - t₂| ≤ K * |t₁ - t₂| := h3.trans hL
  have h6 : |t₁ - t₂| = 0 := by
    have := abs_nonneg (t₁ - t₂)
    nlinarith
  have := abs_eq_zero.mp h6
  linarith

theorem W3a_Larmor_transverse_alg (α β : ℝ) (n a : Vec)
    (hn : n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1) :
    ‖α • n + β • cross n (cross n a)‖ ^ 2
        - (inner ℝ (α • n + β • cross n (cross n a)) n : ℝ) ^ 2
      = β ^ 2 * (‖a‖ ^ 2 - (inner ℝ a n : ℝ) ^ 2) := by
  rw [W3a_Larmor_normsq, W3a_Larmor_inner, W3a_Larmor_normsq a, W3a_Larmor_inner a n]
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, W3a_Larmor_cross0, W3a_Larmor_cross1,
    W3a_Larmor_cross2]
  linear_combination
    (-α ^ 2 * (n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2)
      + β ^ 2 * ((n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 + 1) * (a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2)
        - (n 0 * a 0 + n 1 * a 1 + n 2 * a 2) ^ 2)) * hn

theorem W3a_Larmor_angular_distribution (q ε₀ c R : ℝ) (hε : 0 < ε₀) (hc : 0 < c) (hR : 0 < R)
    (w : ℝ → Vec) (hw0 : w 0 = 0) (hv0 : deriv w 0 = 0) (x : Vec) (hx : ‖x‖ = R) :
    inner ℝ (poynting ε₀ c (lwE q ε₀ c w 0 x) (lwB q ε₀ c w 0 x)) (R⁻¹ • x)
      = q ^ 2 * (‖deriv (deriv w) 0‖ ^ 2 - (inner ℝ (deriv (deriv w) 0) (R⁻¹ • x) : ℝ) ^ 2)
        / (16 * Real.pi ^ 2 * ε₀ * c ^ 3 * R ^ 2) := by
  set a := deriv (deriv w) 0 with ha
  set n : Vec := R⁻¹ • x with hn
  have hnn : ‖n‖ = 1 := by
    rw [hn, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hR, hx, inv_mul_cancel₀ hR.ne']
  have hn2 : n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1 := by
    rw [← W3a_Larmor_normsq, hnn]; norm_num
  have hB : lwB q ε₀ c w 0 x = c⁻¹ • cross n (lwE q ε₀ c w 0 x) := by
    simp [lwB, hw0, hx, hn]
  have hE : lwE q ε₀ c w 0 x
      = (q / (4 * Real.pi * ε₀) * (1 / R ^ 2)) • n
        + (q / (4 * Real.pi * ε₀) * (1 / (c ^ 2 * R))) • cross n (cross n a) := by
    ext i
    fin_cases i <;>
      simp [lwE, hw0, hv0, hx, hn, ha, W3a_Larmor_cross0, W3a_Larmor_cross1,
        W3a_Larmor_cross2] <;> ring
  rw [hB, solution _ _ _ _ hnn, hE, W3a_Larmor_transverse_alg _ _ _ _ hn2]
  field_simp
  ring

theorem W3a_Larmor_pd (F : Vec → Vec) (x : Vec) (hF : DifferentiableAt ℝ F x) (j i : Fin 3) :
    partialDeriv F j i x = fderiv ℝ (fun y => F y i) x (EuclideanSpace.single j 1) := by
  have h : HasFDerivAt (fun y => F y i)
      ((PiLp.proj 2 (fun _ : Fin 3 => ℝ) i).comp (fderiv ℝ F x)) x :=
    (PiLp.hasStrictFDerivAt_apply (𝕜 := ℝ) 2 (F x) i).hasFDerivAt.comp x hF.hasFDerivAt
  rw [h.fderiv]
  simp [partialDeriv]

theorem W3a_Larmor_poynting_theorem (ε₀ c : ℝ) (hε : 0 < ε₀) (hc : 0 < c)
    (ρ : ℝ → Vec → ℝ) (J E B : ℝ → Vec → Vec)
    (hmax : IsMaxwell ε₀ c ρ J E B)
    (hEx : ∀ t, Differentiable ℝ (E t)) (hBx : ∀ t, Differentiable ℝ (B t))
    (hEt : ∀ x, Differentiable ℝ fun s => E s x) (hBt : ∀ x, Differentiable ℝ fun s => B s x)
    (t : ℝ) (x : Vec) :
    deriv (fun s => energyDensity ε₀ c (E s x) (B s x)) t
        + divg (fun y => poynting ε₀ c (E t y) (B t y)) x
      = -inner ℝ (J t x) (E t x) := by
  -- time derivatives of components
  have hEc : ∀ a : Fin 3, HasDerivAt (fun s => E s x a) (deriv (fun s => E s x) t a) t :=
    fun a => by
      have h := (PiLp.hasStrictFDerivAt_apply (𝕜 := ℝ) 2 (E t x) a).hasFDerivAt.comp_hasDerivAt t
        ((hEt x) t).hasDerivAt
      exact h
  have hBc : ∀ a : Fin 3, HasDerivAt (fun s => B s x a) (deriv (fun s => B s x) t a) t :=
    fun a => by
      have h := (PiLp.hasStrictFDerivAt_apply (𝕜 := ℝ) 2 (B t x) a).hasFDerivAt.comp_hasDerivAt t
        ((hBt x) t).hasDerivAt
      exact h
  have hEn : (fun s => energyDensity ε₀ c (E s x) (B s x)) = fun s =>
      ε₀ / 2 * ((E s x 0 * E s x 0 + E s x 1 * E s x 1 + E s x 2 * E s x 2)
        + c ^ 2 * (B s x 0 * B s x 0 + B s x 1 * B s x 1 + B s x 2 * B s x 2)) := by
    funext s
    simp only [energyDensity, W3a_Larmor_normsq]
    ring
  have hd1 : deriv (fun s => energyDensity ε₀ c (E s x) (B s x)) t
      = ε₀ * ((E t x 0 * deriv (fun s => E s x) t 0 + E t x 1 * deriv (fun s => E s x) t 1
          + E t x 2 * deriv (fun s => E s x) t 2)
        + c ^ 2 * (B t x 0 * deriv (fun s => B s x) t 0 + B t x 1 * deriv (fun s => B s x) t 1
          + B t x 2 * deriv (fun s => B s x) t 2)) := by
    rw [hEn]
    exact ((((((hEc 0).mul (hEc 0)).add ((hEc 1).mul (hEc 1))).add ((hEc 2).mul (hEc 2))).add
      (((((hBc 0).mul (hBc 0)).add ((hBc 1).mul (hBc 1))).add
        ((hBc 2).mul (hBc 2))).const_mul (c ^ 2))).const_mul (ε₀ / 2)).deriv.trans (by ring)
  -- spatial derivatives
  have hdE : ∀ a : Fin 3, DifferentiableAt ℝ (fun y => E t y a) x :=
    fun a => (differentiableAt_euclidean.1 (hEx t x)) a
  have hdB : ∀ a : Fin 3, DifferentiableAt ℝ (fun y => B t y a) x :=
    fun a => (differentiableAt_euclidean.1 (hBx t x)) a
  have hS0 : (fun y => poynting ε₀ c (E t y) (B t y) 0)
      = fun y => ε₀ * c ^ 2 * (E t y 1 * B t y 2 - E t y 2 * B t y 1) := by
    funext y; simp only [poynting, PiLp.smul_apply, smul_eq_mul, W3a_Larmor_cross0]
  have hS1 : (fun y => poynting ε₀ c (E t y) (B t y) 1)
      = fun y => ε₀ * c ^ 2 * (E t y 2 * B t y 0 - E t y 0 * B t y 2) := by
    funext y; simp only [poynting, PiLp.smul_apply, smul_eq_mul, W3a_Larmor_cross1]
  have hS2 : (fun y => poynting ε₀ c (E t y) (B t y) 2)
      = fun y => ε₀ * c ^ 2 * (E t y 0 * B t y 1 - E t y 1 * B t y 0) := by
    funext y; simp only [poynting, PiLp.smul_apply, smul_eq_mul, W3a_Larmor_cross2]
  have hS0d := ((((hdE 1).hasFDerivAt.mul (hdB 2).hasFDerivAt).sub
    ((hdE 2).hasFDerivAt.mul (hdB 1).hasFDerivAt)).const_mul (ε₀ * c ^ 2))
  have hS1d := ((((hdE 2).hasFDerivAt.mul (hdB 0).hasFDerivAt).sub
    ((hdE 0).hasFDerivAt.mul (hdB 2).hasFDerivAt)).const_mul (ε₀ * c ^ 2))
  have hS2d := ((((hdE 0).hasFDerivAt.mul (hdB 1).hasFDerivAt).sub
    ((hdE 1).hasFDerivAt.mul (hdB 0).hasFDerivAt)).const_mul (ε₀ * c ^ 2))
  have hSdiff : DifferentiableAt ℝ (fun y => poynting ε₀ c (E t y) (B t y)) x := by
    rw [differentiableAt_euclidean]
    intro i
    fin_cases i
    · show DifferentiableAt ℝ (fun y => poynting ε₀ c (E t y) (B t y) 0) x
      rw [hS0]; exact hS0d.differentiableAt
    · show DifferentiableAt ℝ (fun y => poynting ε₀ c (E t y) (B t y) 1) x
      rw [hS1]; exact hS1d.differentiableAt
    · show DifferentiableAt ℝ (fun y => poynting ε₀ c (E t y) (B t y) 2) x
      rw [hS2]; exact hS2d.differentiableAt
  have hdiv : divg (fun y => poynting ε₀ c (E t y) (B t y)) x
      = fderiv ℝ (fun y => ε₀ * c ^ 2 * (E t y 1 * B t y 2 - E t y 2 * B t y 1)) x
            (EuclideanSpace.single 0 1)
        + fderiv ℝ (fun y => ε₀ * c ^ 2 * (E t y 2 * B t y 0 - E t y 0 * B t y 2)) x
            (EuclideanSpace.single 1 1)
        + fderiv ℝ (fun y => ε₀ * c ^ 2 * (E t y 0 * B t y 1 - E t y 1 * B t y 0)) x
            (EuclideanSpace.single 2 1) := by
    unfold divg
    rw [Fin.sum_univ_three, W3a_Larmor_pd _ _ hSdiff, W3a_Larmor_pd _ _ hSdiff,
      W3a_Larmor_pd _ _ hSdiff, hS0, hS1, hS2]
  have e0 : fderiv ℝ (fun y => ε₀ * c ^ 2 * (E t y 1 * B t y 2 - E t y 2 * B t y 1)) x = _ :=
    hS0d.fderiv
  have e1 : fderiv ℝ (fun y => ε₀ * c ^ 2 * (E t y 2 * B t y 0 - E t y 0 * B t y 2)) x = _ :=
    hS1d.fderiv
  have e2 : fderiv ℝ (fun y => ε₀ * c ^ 2 * (E t y 0 * B t y 1 - E t y 1 * B t y 0)) x = _ :=
    hS2d.fderiv
  rw [e0, e1, e2] at hdiv
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, smul_eq_mul] at hdiv
  -- Faraday and Ampère in components
  have hfar := hmax.faraday t x
  have hamp := hmax.ampere t x
  have f0 := congrArg (fun v : Vec => v 0) hfar
  have f1 := congrArg (fun v : Vec => v 1) hfar
  have f2 := congrArg (fun v : Vec => v 2) hfar
  have a0 := congrArg (fun v : Vec => v 0) hamp
  have a1 := congrArg (fun v : Vec => v 1) hamp
  have a2 := congrArg (fun v : Vec => v 2) hamp
  simp only [W3a_Larmor_curl0, W3a_Larmor_curl1, W3a_Larmor_curl2, PiLp.neg_apply,
    PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    W3a_Larmor_pd _ _ (hEx t x), W3a_Larmor_pd _ _ (hBx t x)] at f0 f1 f2 a0 a1 a2
  have hk1 : ε₀ * c ^ 2 * (1 / (ε₀ * c ^ 2)) = 1 := by field_simp
  have hk2 : c ^ 2 * (1 / c ^ 2) = 1 := by field_simp
  rw [hd1, hdiv, W3a_Larmor_inner]
  linear_combination
    (ε₀ * c ^ 2 * B t x 0) * f0 + (ε₀ * c ^ 2 * B t x 1) * f1 + (ε₀ * c ^ 2 * B t x 2) * f2
    - (ε₀ * c ^ 2 * E t x 0) * a0 - (ε₀ * c ^ 2 * E t x 1) * a1 - (ε₀ * c ^ 2 * E t x 2) * a2
    - (J t x 0 * E t x 0 + J t x 1 * E t x 1 + J t x 2 * E t x 2) * hk1
    - (ε₀ * (E t x 0 * deriv (fun s => E s x) t 0 + E t x 1 * deriv (fun s => E s x) t 1
          + E t x 2 * deriv (fun s => E s x) t 2)) * hk2
