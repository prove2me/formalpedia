-- Prove2me | solution 1 for JailletLu.ratio_bound_general_rates
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-05T13:53:32.503193+00:00
-- url     : https://prove2.me/submissions/a3681381-a38d-4a78-a3ee-0b05ac5e08a7

import Mathlib
import Definitions.Def_JailletLu_LP4Feasible
import Definitions.Def_JailletLu_IsAdmissibleOrder
import Definitions.Def_JailletLu_fTot
import Definitions.Def_JailletLu_third

set_option autoImplicit false
set_option linter.all false

open JailletLu



lemma jl_h_zero (y : ℝ) : h y 0 = 1 - Real.exp (-y) := by
  unfold h
  split_ifs with hy
  · subst hy; simp
  · have : y ≠ 0 := fun e => hy e.symm
    field_simp
    simp

lemma jl_g_integral (y x : ℝ) :
    g y x = ∫ θ in (0:ℝ)..1, y * Real.exp (-(y*θ)) * (1 - Real.exp (-(x*(1-θ)))) := by
  have hh0 := jl_h_zero y
  have hcomb : ∀ θ : ℝ, Real.exp (-(y*θ)) * Real.exp (-(x*(1-θ)))
      = Real.exp (-x) * Real.exp (-((y-x)*θ)) := by
    intro θ; rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  by_cases hxy : x = y
  · subst hxy
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun θ => -Real.exp (-(x*θ)) - x * Real.exp (-x) * θ)]
    · rw [show g x x = h x 0 - h x x from rfl, hh0]
      unfold h; rw [if_pos rfl]; simp; ring
    · intro θ _
      have h1 : HasDerivAt (fun θ : ℝ => -(x*θ)) (-x) θ := by
        exact ((hasDerivAt_id' θ).const_mul x).neg.congr_deriv (by ring)
      have h2 := h1.exp
      have h3 := (hasDerivAt_id' θ).const_mul (x * Real.exp (-x))
      refine (h2.neg.sub h3).congr_deriv ?_
      have := hcomb θ
      simp only [sub_self, zero_mul, neg_zero, Real.exp_zero, mul_one] at this
      linear_combination x * this
    · apply Continuous.intervalIntegrable; fun_prop
  · have hne : y - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun θ => -Real.exp (-(y*θ)) + y / (y - x) * (Real.exp (-x) * Real.exp (-((y-x)*θ))))]
    · rw [show g y x = h y 0 - h y x from rfl, hh0]
      unfold h
      rw [if_neg hxy]
      simp only [mul_one, mul_zero, neg_zero, Real.exp_zero, sub_zero]
      have e1 : Real.exp (-x) * Real.exp (-(y - x)) = Real.exp (-y) := by
        rw [← Real.exp_add]; ring_nf
      rw [e1]; field_simp; ring
    · intro θ _
      have h1 : HasDerivAt (fun θ : ℝ => -(y*θ)) (-y) θ := by
        exact ((hasDerivAt_id' θ).const_mul y).neg.congr_deriv (by ring)
      have h4 : HasDerivAt (fun θ : ℝ => -((y-x)*θ)) (-(y-x)) θ := by
        exact ((hasDerivAt_id' θ).const_mul (y-x)).neg.congr_deriv (by ring)
      have h5 := ((h4.exp).const_mul (Real.exp (-x))).const_mul (y / (y - x))
      refine ((h1.exp.neg).add h5).congr_deriv ?_
      have e2 : y / (y - x) * (Real.exp (-x) * (Real.exp (-((y - x) * θ)) * -(y - x)))
          = -(y * (Real.exp (-x) * Real.exp (-((y - x) * θ)))) := by field_simp
      rw [e2]
      linear_combination y * hcomb θ
    · apply Continuous.intervalIntegrable; fun_prop

lemma jl_int_one_sub_mul_exp : ∫ θ in (0:ℝ)..1, (1 - θ) * Real.exp (-θ) = Real.exp (-1) := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun θ => θ * Real.exp (-θ))]
  · simp
  · intro θ _
    have h1 : HasDerivAt (fun θ : ℝ => -θ) (-1) θ := (hasDerivAt_id' θ).neg
    refine ((hasDerivAt_id' θ).mul h1.exp).congr_deriv ?_
    ring
  · apply Continuous.intervalIntegrable; fun_prop





lemma jl_F_nonneg {x θ : ℝ} (hx : 0 ≤ x) (hθ : θ ≤ 1) : 0 ≤ 1 - Real.exp (-(x*(1-θ))) := by
  have : 0 ≤ x*(1-θ) := mul_nonneg hx (by linarith)
  have : Real.exp (-(x*(1-θ))) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  linarith

lemma jl_F_le_lin (x θ : ℝ) : 1 - Real.exp (-(x*(1-θ))) ≤ x*(1-θ) := by
  have := Real.add_one_le_exp (-(x*(1-θ)))
  linarith

lemma jl_F_le_one (x θ : ℝ) : 1 - Real.exp (-(x*(1-θ))) ≤ 1 := by
  have := Real.exp_pos (-(x*(1-θ))); linarith

lemma jl_w_le {y θ : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    y * Real.exp (-(y*θ)) ≤ 1 * Real.exp (-(1*θ)) := by
  have e : Real.exp (-(1*θ)) = Real.exp (-(y*θ)) * Real.exp (-((1-y)*θ)) := by
    rw [← Real.exp_add]; ring_nf
  have h1 : y ≤ Real.exp (-((1-y)*θ)) := by
    have := Real.add_one_le_exp (-((1-y)*θ))
    nlinarith
  rw [e, one_mul, mul_comm y]
  exact mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le

lemma jl_w_diff_le {f θ : ℝ} (hf0 : 0 ≤ f) (hf1 : f ≤ 1) (hθ0 : 0 ≤ θ) :
    1 * Real.exp (-(1*θ)) - f * Real.exp (-(f*θ)) ≤ 1 - f := by
  have h1 : Real.exp (-(1*θ)) ≤ Real.exp (-(f*θ)) := Real.exp_le_exp.mpr (by nlinarith)
  have h2 : Real.exp (-(f*θ)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  nlinarith

lemma jl_g_nonneg {y x : ℝ} (hy : 0 ≤ y) (hx : 0 ≤ x) : 0 ≤ g y x := by
  rw [jl_g_integral]
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro θ hθ
  exact mul_nonneg (mul_nonneg hy (Real.exp_pos _).le) (jl_F_nonneg hx hθ.2)

lemma jl_g_le_one {y x : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (hx : 0 ≤ x) : g y x ≤ g 1 x := by
  rw [jl_g_integral, jl_g_integral]
  apply intervalIntegral.integral_mono_on (by norm_num)
  · apply Continuous.intervalIntegrable; fun_prop
  · apply Continuous.intervalIntegrable; fun_prop
  intro θ hθ
  exact mul_le_mul_of_nonneg_right (jl_w_le hy0 hy1 hθ.1 hθ.2) (jl_F_nonneg hx hθ.2)

lemma jl_g_le_lin {f x : ℝ} (hf0 : 0 ≤ f) (hf1 : f ≤ 1) (hx : 0 ≤ x) :
    g f x ≤ x * Real.exp (-1) := by
  calc g f x ≤ g 1 x := jl_g_le_one hf0 hf1 hx
    _ ≤ ∫ θ in (0:ℝ)..1, x * ((1 - θ) * Real.exp (-θ)) := by
        rw [jl_g_integral]
        apply intervalIntegral.integral_mono_on (by norm_num)
        · apply Continuous.intervalIntegrable; fun_prop
        · apply Continuous.intervalIntegrable; fun_prop
        intro θ hθ
        have := jl_F_le_lin x θ
        have he := Real.exp_pos (-θ)
        simp only [one_mul]
        nlinarith
    _ = x * Real.exp (-1) := by
        rw [intervalIntegral.integral_const_mul, jl_int_one_sub_mul_exp]

lemma jl_int_lin : ∫ θ in (0:ℝ)..1, (1 - θ) = 1/2 := by
  rw [intervalIntegral.integral_sub (by simp) (by simp)]
  simp; norm_num

lemma jl_g_diff {f x : ℝ} (hf0 : 0 ≤ f) (hf1 : f ≤ 1) (hx : 0 ≤ x) :
    g 1 x - g f x ≤ (1 - f) * x / 2 := by
  rw [jl_g_integral, jl_g_integral, ← intervalIntegral.integral_sub]
  · calc _ ≤ ∫ θ in (0:ℝ)..1, ((1 - f) * x) * (1 - θ) := by
          apply intervalIntegral.integral_mono_on (by norm_num)
          · apply Continuous.intervalIntegrable; fun_prop
          · apply Continuous.intervalIntegrable; fun_prop
          intro θ hθ
          have h1 := jl_w_diff_le hf0 hf1 hθ.1
          have h2 := jl_w_le hf0 hf1 hθ.1 hθ.2
          have h3 := jl_F_le_lin x θ
          have h4 := jl_F_nonneg hx hθ.2
          have h5 : 0 ≤ x * (1 - θ) := mul_nonneg hx (by linarith [hθ.2])
          rw [← sub_mul]
          calc _ ≤ (1 - f) * (1 - Real.exp (-(x * (1 - θ)))) :=
                mul_le_mul_of_nonneg_right h1 h4
            _ ≤ (1 - f) * (x * (1 - θ)) := mul_le_mul_of_nonneg_left h3 (by linarith)
            _ = _ := by ring
      _ = (1 - f) * x / 2 := by rw [intervalIntegral.integral_const_mul, jl_int_lin]; ring
  · apply Continuous.intervalIntegrable; fun_prop
  · apply Continuous.intervalIntegrable; fun_prop

lemma jl_g_le_W {f x : ℝ} (hf : 0 ≤ f) (hx : 0 ≤ x) : g f x ≤ 1 - Real.exp (-f) := by
  have hint : ∫ θ in (0:ℝ)..1, f * Real.exp (-(f*θ)) = 1 - Real.exp (-f) := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun θ => -Real.exp (-(f*θ)))]
    · simp; ring
    · intro θ _
      have h1 : HasDerivAt (fun θ : ℝ => -(f*θ)) (-f) θ :=
        ((hasDerivAt_id' θ).const_mul f).neg.congr_deriv (by ring)
      exact h1.exp.neg.congr_deriv (by ring)
    · apply Continuous.intervalIntegrable; fun_prop
  rw [jl_g_integral, ← hint]
  apply intervalIntegral.integral_mono_on (by norm_num)
  · apply Continuous.intervalIntegrable; fun_prop
  · apply Continuous.intervalIntegrable; fun_prop
  intro θ _
  have := jl_F_le_one x θ
  have := mul_nonneg hf (Real.exp_pos (-(f*θ))).le
  nlinarith

lemma jl_g_concave {f a b t : ℝ} (hf : 0 ≤ f) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - t) * g f a + t * g f b ≤ g f ((1 - t) * a + t * b) := by
  rw [jl_g_integral, jl_g_integral, jl_g_integral, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add]
  · apply intervalIntegral.integral_mono_on (by norm_num)
    · apply Continuous.intervalIntegrable; fun_prop
    · apply Continuous.intervalIntegrable; fun_prop
    intro θ _
    have hc := convexOn_exp.2 (Set.mem_univ (-(a*(1-θ)))) (Set.mem_univ (-(b*(1-θ))))
      (by linarith : (0:ℝ) ≤ 1 - t) ht0 (by ring)
    simp only [smul_eq_mul] at hc
    have e : (1 - t) * -(a * (1 - θ)) + t * -(b * (1 - θ)) = -(((1 - t) * a + t * b) * (1 - θ)) := by
      ring
    rw [e] at hc
    have hw := mul_nonneg hf (Real.exp_pos (-(f*θ))).le
    nlinarith
  · apply Continuous.intervalIntegrable; fun_prop
  · apply Continuous.intervalIntegrable; fun_prop

lemma jl_g_zero (f : ℝ) : g f 0 = 0 := by
  unfold g; simp

lemma jl_g_self (f : ℝ) : g f f = 1 - Real.exp (-f) - f * Real.exp (-f) := by
  have := jl_g_zero f
  unfold g at *
  unfold h; simp only [if_pos rfl]
  rw [show (if (0:ℝ) = f then f * Real.exp (-f) else f / (f - 0) * (Real.exp (-0) - Real.exp (-f)))
      = h f 0 from rfl]
  unfold h
  split_ifs with h0
  · subst h0; simp
  · have : f ≠ 0 := fun e => h0 e.symm
    field_simp; simp





lemma jl_int_w (f : ℝ) : ∫ θ in (0:ℝ)..1, f * Real.exp (-(f*θ)) = 1 - Real.exp (-f) := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun θ => -Real.exp (-(f*θ)))]
  · simp; ring
  · intro θ _
    have h1 : HasDerivAt (fun θ : ℝ => -(f*θ)) (-f) θ :=
      ((hasDerivAt_id' θ).const_mul f).neg.congr_deriv (by ring)
    exact h1.exp.neg.congr_deriv (by ring)
  · apply Continuous.intervalIntegrable; fun_prop

lemma jl_int_lin4 (A B C D : ℝ → ℝ) (hA : Continuous A) (hB : Continuous B) (hC : Continuous C)
    (hD : Continuous D) (a b c : ℝ) :
    ∫ θ in (0:ℝ)..1, (A θ - a * B θ - b * C θ + c * D θ)
      = (∫ θ in (0:ℝ)..1, A θ) - a * (∫ θ in (0:ℝ)..1, B θ) - b * (∫ θ in (0:ℝ)..1, C θ)
        + c * (∫ θ in (0:ℝ)..1, D θ) := by
  rw [intervalIntegral.integral_add, intervalIntegral.integral_sub, intervalIntegral.integral_sub,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  all_goals (apply Continuous.intervalIntegrable; fun_prop)

lemma jl_sign {u v τ τ' : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 ≤ (Real.exp (-(u*τ')) - Real.exp (-(u*τ))) * (Real.exp (-(v*τ')) - Real.exp (-(v*τ))) := by
  rcases le_total τ τ' with h | h
  · have h1 : Real.exp (-(u*τ')) ≤ Real.exp (-(u*τ)) := Real.exp_le_exp.mpr (by nlinarith)
    have h2 : Real.exp (-(v*τ')) ≤ Real.exp (-(v*τ)) := Real.exp_le_exp.mpr (by nlinarith)
    nlinarith
  · have h1 : Real.exp (-(u*τ)) ≤ Real.exp (-(u*τ')) := Real.exp_le_exp.mpr (by nlinarith)
    have h2 : Real.exp (-(v*τ)) ≤ Real.exp (-(v*τ')) := Real.exp_le_exp.mpr (by nlinarith)
    nlinarith

lemma jl_cheb {f u v : ℝ} (hf : 0 < f) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    g f u * g f v ≤ (1 - Real.exp (-f)) * (g f u + g f v - g f (u + v)) := by
  set W := 1 - Real.exp (-f) with hW
  have hWpos : 0 < W := by
    have : Real.exp (-f) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  -- identity
  have hid : g f u + g f v - g f (u + v) = ∫ θ in (0:ℝ)..1,
      f * Real.exp (-(f*θ)) * (1 - Real.exp (-(u*(1-θ)))) * (1 - Real.exp (-(v*(1-θ)))) := by
    rw [jl_g_integral, jl_g_integral, jl_g_integral, ← intervalIntegral.integral_add,
      ← intervalIntegral.integral_sub]
    · apply intervalIntegral.integral_congr
      intro θ _
      simp only
      have e : Real.exp (-((u + v) * (1 - θ))) = Real.exp (-(u*(1-θ))) * Real.exp (-(v*(1-θ))) := by
        rw [← Real.exp_add]; ring_nf
      rw [e]; ring
    all_goals (apply Continuous.intervalIntegrable; fun_prop)
  rcases hv.eq_or_lt with hv0 | hv0
  · subst hv0
    have : g f 0 = 0 := by unfold g; simp
    rw [this]; simp
  -- crossing point
  have hgv0 : 0 ≤ g f v := by
    rw [jl_g_integral]
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro θ hθ
    have : Real.exp (-(v*(1-θ))) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [hθ.2])
    have := mul_nonneg hf.le (Real.exp_pos (-(f*θ))).le
    nlinarith
  have hgv1 : g f v ≤ W * (1 - Real.exp (-v)) := by
    rw [jl_g_integral, hW, ← jl_int_w, ← intervalIntegral.integral_mul_const]
    apply intervalIntegral.integral_mono_on (by norm_num)
    · apply Continuous.intervalIntegrable; fun_prop
    · apply Continuous.intervalIntegrable; fun_prop
    intro θ hθ
    have : Real.exp (-v) ≤ Real.exp (-(v*(1-θ))) := Real.exp_le_exp.mpr (by nlinarith [hθ.1])
    have := mul_nonneg hf.le (Real.exp_pos (-(f*θ))).le
    nlinarith
  set d := g f v / W with hd
  have hd0 : 0 ≤ d := div_nonneg hgv0 hWpos.le
  have hd1 : d ≤ 1 - Real.exp (-v) := by rw [hd, div_le_iff₀ hWpos]; linarith
  have h1d : 0 < 1 - d := by have := Real.exp_pos (-v); linarith
  set τs := -Real.log (1 - d) / v with hτs
  have hexp_v : Real.exp (-(v*τs)) = 1 - d := by
    rw [hτs, show -(v * (-Real.log (1 - d) / v)) = Real.log (1 - d) by field_simp]
    exact Real.exp_log h1d
  set p := 1 - Real.exp (-(u*τs)) with hp
  have hnonneg : 0 ≤ ∫ θ in (0:ℝ)..1,
      (f * Real.exp (-(f*θ)) * (1 - Real.exp (-(u*(1-θ)))) * (1 - Real.exp (-(v*(1-θ))))
        - d * (f * Real.exp (-(f*θ)) * (1 - Real.exp (-(u*(1-θ)))))
        - p * (f * Real.exp (-(f*θ)) * (1 - Real.exp (-(v*(1-θ)))))
        + (p * d) * (f * Real.exp (-(f*θ)))) := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro θ _
    have hs := jl_sign (τ := 1 - θ) (τ' := τs) hu hv
    rw [hexp_v] at hs
    have hw := mul_nonneg hf.le (Real.exp_pos (-(f*θ))).le
    have : (f * Real.exp (-(f*θ)) * (1 - Real.exp (-(u*(1-θ)))) * (1 - Real.exp (-(v*(1-θ))))
        - d * (f * Real.exp (-(f*θ)) * (1 - Real.exp (-(u*(1-θ)))))
        - p * (f * Real.exp (-(f*θ)) * (1 - Real.exp (-(v*(1-θ)))))
        + (p * d) * (f * Real.exp (-(f*θ))))
        = (f * Real.exp (-(f*θ))) * ((Real.exp (-(u * τs)) - Real.exp (-(u * (1 - θ)))) *
          (1 - d - Real.exp (-(v * (1 - θ))))) := by rw [hp]; ring
    rw [this]; exact mul_nonneg hw hs
  rw [jl_int_lin4 _ _ _ _ (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop),
    ← jl_g_integral, ← jl_g_integral, jl_int_w, ← hid] at hnonneg
  have hgvd : g f v = d * W := by rw [hd]; field_simp
  rw [hgvd] at hnonneg ⊢
  have hgu0 : 0 ≤ g f u := by
    rw [jl_g_integral]
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro θ hθ
    have : Real.exp (-(u*(1-θ))) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [hθ.2])
    have := mul_nonneg hf.le (Real.exp_pos (-(f*θ))).le
    nlinarith
  nlinarith



lemma jl_exp_up4 {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Real.exp t ≤ 1 + t + t^2/2 + t^3/6 + t^4*(5/96) := by
  have h := Real.exp_bound (x := t) (by rw [abs_of_nonneg ht0]; exact ht1) (n := 4) (by norm_num)
  rw [abs_of_nonneg ht0] at h
  simp [Finset.sum_range_succ, Nat.factorial] at h
  have := (abs_le.mp h).2
  norm_num at this
  linarith

lemma jl_exp_neg_up6 {f : ℝ} (hf0 : 0 ≤ f) (hf1 : f ≤ 1) :
    Real.exp (-f) ≤ 1 - f + f^2/2 - f^3/6 + f^4/24 - f^5/120 + f^6*(7/4320) := by
  have h := Real.exp_bound (x := -f) (by rw [abs_neg, abs_of_nonneg hf0]; exact hf1) (n := 6)
    (by norm_num)
  rw [abs_neg, abs_of_nonneg hf0] at h
  simp [Finset.sum_range_succ, Nat.factorial] at h
  have := (abs_le.mp h).2
  norm_num at this
  nlinarith

lemma jl_E1_poly (f ε X : ℝ) (hf0 : 0 ≤ f) (hf1 : f ≤ 1) (ha0 : 0.3678 ≤ ε) (ha1 : ε ≤ 0.3679)
    (hX : X ≤ 1 - f + f^2/2 - f^3/6 + f^4/24 - f^5/120 + f^6*(7/4320)) :
    0 ≤ 1 - X + ε*(1 - X - f*X - f^2*((1 - f)/2*ε + ((1 - f)/2)^2/2)) - 0.706*f := by
  set U := 1 - f + f^2/2 - f^3/6 + f^4/24 - f^5/120 + f^6*(7/4320) with hU
  have hK : 0 ≤ 1 + ε + ε*f := by nlinarith
  have hmono : 1 - U + ε*(1 - U - f*U - f^2*((1 - f)/2*ε + ((1 - f)/2)^2/2)) - 0.706*f
      ≤ 1 - X + ε*(1 - X - f*X - f^2*((1 - f)/2*ε + ((1 - f)/2)^2/2)) - 0.706*f := by
    nlinarith [mul_le_mul_of_nonneg_right hX hK]
  refine le_trans ?_ hmono
  have hid : 1 - U + ε*(1 - U - f*U - f^2*((1 - f)/2*ε + ((1 - f)/2)^2/2)) - 0.706*f
      = f * (0.294 + (-1/2 + 3*ε/8 - ε^2/2)*f + (1/6 - ε/12 + ε^2/2)*f^2 - (1/24)*f^3
          + (1/120 - ε/30)*f^4 + (-7/4320 + 29*ε/4320)*f^5 + (-7*ε/4320)*f^6) := by
    rw [hU]; ring
  rw [hid]
  apply mul_nonneg hf0
  have e2 : ε^2 ≤ 0.3679^2 := pow_le_pow_left₀ (by linarith) ha1 2
  have e2' : 0.3678^2 ≤ ε^2 := pow_le_pow_left₀ (by norm_num) ha0 2
  have d2 : -0.4298 ≤ -1/2 + 3*ε/8 - ε^2/2 := by nlinarith
  have d3 : 0.2036 ≤ 1/6 - ε/12 + ε^2/2 := by nlinarith
  have d5 : -0.004 ≤ 1/120 - ε/30 := by nlinarith
  have d6 : 0 ≤ -7/4320 + 29*ε/4320 := by nlinarith
  have d7 : -0.0006 ≤ -7*ε/4320 := by nlinarith
  have f2 : 0 ≤ f^2 := by positivity
  have f3 : f^3 ≤ 1 := pow_le_one₀ hf0 hf1
  have f4 : f^4 ≤ 1 := pow_le_one₀ hf0 hf1
  have f4' : 0 ≤ f^4 := by positivity
  have f5 : 0 ≤ f^5 := by positivity
  have f6 : f^6 ≤ 1 := pow_le_one₀ hf0 hf1
  have f6' : 0 ≤ f^6 := by positivity
  have q : 0 ≤ (1 - f)*(1.1 - f) := mul_nonneg (by linarith) (by linarith)
  nlinarith [mul_le_mul_of_nonneg_right d2 hf0, mul_le_mul_of_nonneg_right d3 f2,
    mul_le_mul_of_nonneg_right d5 f4', mul_nonneg d6 f5, mul_le_mul_of_nonneg_right d7 f6']

lemma jl_E3 {f : ℝ} (hf0 : 0 ≤ f) (hf1 : f ≤ 0.3101) : 0.706 * f ≤ 1 - Real.exp (-f) := by
  have h := jl_exp_neg_up6 hf0 (by linarith)
  have f2 : 0 ≤ f^2 := by positivity
  have f4 : 0 ≤ f^4 := by positivity
  have f6 : 0 ≤ f^6 := by positivity
  have a3 : f^3 ≥ 0 := by positivity
  have a4 : f^4 ≤ f^3 := by nlinarith
  have a5 : f^5 ≥ 0 := by positivity
  have a6 : f^6 ≤ f^5 := by nlinarith [pow_le_one₀ hf0 (by linarith : f ≤ 1) (n := 1)]
  nlinarith

lemma jl_F6 {f : ℝ} (hf : 0 < f) (hf1 : f ≤ 1) {ι : Type*} [DecidableEq ι] (x : ι → ℝ) (hx : ∀ j, 0 ≤ x j)
    (T : Finset ι) (hT : ∑ j ∈ T, x j ≤ 1) :
    g f (∑ j ∈ T, x j) ≤ (∑ j ∈ T, g f (x j))
      - ((∑ j ∈ T, g f (x j))^2 - ∑ j ∈ T, (g f (x j))^2) / 2 := by
  induction T using Finset.induction_on with
  | empty => simp [jl_g_zero]
  | insert a T ha ih =>
    rw [Finset.sum_insert ha] at hT
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.sum_insert ha]
    set S := ∑ j ∈ T, x j with hS
    set A := ∑ j ∈ T, g f (x j) with hA
    set Q := ∑ j ∈ T, (g f (x j))^2 with hQ
    have hS0 : 0 ≤ S := Finset.sum_nonneg (fun j _ => hx j)
    have hS1 : S ≤ 1 := by linarith [hx a]
    have ih' := ih hS1
    set M := A - (A^2 - Q)/2 with hM
    set W := 1 - Real.exp (-f) with hW
    have hWpos : 0 < W := by
      have : Real.exp (-f) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
      linarith
    have hch := jl_cheb hf hS0 (hx a)
    rw [add_comm S (x a)] at hch
    have hv0 : 0 ≤ g f (x a) := jl_g_nonneg hf.le (hx a)
    have hvW : g f (x a) ≤ W := jl_g_le_W hf.le (hx a)
    have hA0 : 0 ≤ A := Finset.sum_nonneg (fun j _ => jl_g_nonneg hf.le (hx j))
    have hQ0 : 0 ≤ Q := Finset.sum_nonneg (fun j _ => sq_nonneg _)
    have hAle : A ≤ S * Real.exp (-1) := by
      rw [hA, hS, Finset.sum_mul]
      exact Finset.sum_le_sum (fun j _ => jl_g_le_lin hf.le hf1 (hx j))
    have hε : Real.exp (-1) ≤ Real.exp (-f) := Real.exp_le_exp.mpr (by linarith)
    have hMW : W * A ≤ M := by
      have : A ≤ 2 * Real.exp (-f) := by nlinarith [Real.exp_pos (-1)]
      rw [hM, hW]; nlinarith
    have h1 : g f S * (W - g f (x a)) ≤ M * (W - g f (x a)) :=
      mul_le_mul_of_nonneg_right ih' (by linarith)
    have h2 : 0 ≤ g f (x a) * (M - W * A) := mul_nonneg hv0 (by linarith)
    have key : W * g f (x a + S) ≤ W * ((g f (x a) + A) - ((g f (x a) + A)^2 - ((g f (x a))^2 + Q))/2) := by
      nlinarith
    exact le_of_mul_le_mul_left key hWpos

lemma jl_eps_bounds : 0.3678794411 < Real.exp (-1) ∧ Real.exp (-1) < 0.3678794416 := by
  have hprod : Real.exp (-1) * Real.exp 1 = 1 := by rw [← Real.exp_add]; simp
  have h1 := Real.exp_one_lt_d9
  have h2 := Real.exp_one_gt_d9
  have hp := Real.exp_pos (-1)
  constructor <;> nlinarith

lemma jl_g_shift (f c : ℝ) (hc : c ≠ 0) :
    g f (f - c) = 1 - Real.exp (-f) - f / c * (Real.exp (-(f - c)) - Real.exp (-f)) := by
  rw [show g f (f - c) = h f 0 - h f (f - c) from rfl, jl_h_zero]
  unfold h
  rw [if_neg (by intro e; apply hc; linarith)]
  rw [show f - (f - c) = c by ring]

lemma jl_concave_ends {f a b s : ℝ} (hf : 0 ≤ f) (hab : a < b) (has : a ≤ s) (hsb : s ≤ b)
    (C : ℝ) (hC : 0 ≤ C) (ε : ℝ) (hε : 0 ≤ ε)
    (ha : 0 ≤ 1 - Real.exp (-f) + ε * (g f a - a^2 * C) - 0.706 * f)
    (hb : 0 ≤ 1 - Real.exp (-f) + ε * (g f b - b^2 * C) - 0.706 * f) :
    0 ≤ 1 - Real.exp (-f) + ε * (g f s - s^2 * C) - 0.706 * f := by
  set t := (s - a) / (b - a) with ht
  have hba : 0 < b - a := by linarith
  have ht0 : 0 ≤ t := div_nonneg (by linarith) hba.le
  have ht1 : t ≤ 1 := by rw [ht, div_le_one hba]; linarith
  have hs : s = (1 - t) * a + t * b := by rw [ht]; field_simp; ring
  have hcv := jl_g_concave (f := f) (a := a) (b := b) hf ht0 ht1
  rw [← hs] at hcv
  have hsq : 0 ≤ (1 - t) * a^2 + t * b^2 - s^2 := by
    rw [hs]; nlinarith [mul_nonneg ht0 (by linarith : (0:ℝ) ≤ 1 - t), sq_nonneg (a - b)]
  have hid : 1 - Real.exp (-f) + ε * (g f s - s^2 * C) - 0.706 * f
      = (1 - t) * (1 - Real.exp (-f) + ε * (g f a - a^2 * C) - 0.706 * f)
        + t * (1 - Real.exp (-f) + ε * (g f b - b^2 * C) - 0.706 * f)
        + ε * (g f s - ((1 - t) * g f a + t * g f b))
        + ε * C * ((1 - t) * a^2 + t * b^2 - s^2) := by ring
  rw [hid]
  have := mul_nonneg (by linarith : (0:ℝ) ≤ 1 - t) ha
  have := mul_nonneg ht0 hb
  have := mul_nonneg hε (by linarith : (0:ℝ) ≤ g f s - ((1 - t) * g f a + t * g f b))
  have := mul_nonneg (mul_nonneg hε hC) hsq
  linarith


lemma jl_main_lower (f : ℝ) (hf : 0 < f) (hf1 : f ≤ 1) {ι : Type*} [DecidableEq ι] (T : Finset ι)
    (x y : ι → ℝ) (hx : ∀ j, 0 ≤ x j) (hxy : ∀ j, x j ≤ y j) (hy : ∀ j, y j ≤ 1)
    (hs : ∑ j ∈ T, x j ≤ f) :
    1 - Real.exp (-f) + Real.exp (-1) * (g f (∑ j ∈ T, x j) - (∑ j ∈ T, x j)^2 *
      ((1 - f)/2 * Real.exp (-1) + ((1 - f)/2)^2/2)) ≤
    1 - Real.exp (-f) + (1 / Real.exp 1) * ∑ j ∈ T, g f (x j)
      - (1 / (2 * Real.exp 1)) * (∑ j ∈ T, g (y j) (x j)) ^ 2
      + (1 / (2 * Real.exp 1)) * ∑ j ∈ T, g f (x j) ^ 2 := by
  set s := ∑ j ∈ T, x j with hsdef
  set ε := Real.exp (-1) with hεdef
  set A := ∑ j ∈ T, g f (x j) with hAdef
  set Q := ∑ j ∈ T, (g f (x j))^2 with hQdef
  set B := ∑ j ∈ T, g 1 (x j) with hBdef
  set Bp := ∑ j ∈ T, g (y j) (x j) with hBpdef
  have e1 : 1 / Real.exp 1 = ε := by rw [hεdef, Real.exp_neg]; ring
  have e2 : 1 / (2 * Real.exp 1) = ε / 2 := by rw [← e1]; field_simp
  rw [e1, e2]
  have hε0 : 0 ≤ ε := (Real.exp_pos _).le
  have hs0 : 0 ≤ s := Finset.sum_nonneg (fun j _ => hx j)
  have hy0 : ∀ j, 0 ≤ y j := fun j => le_trans (hx j) (hxy j)
  have hBp0 : 0 ≤ Bp := Finset.sum_nonneg (fun j _ => jl_g_nonneg (hy0 j) (hx j))
  have hBpB : Bp ≤ B := Finset.sum_le_sum (fun j _ => jl_g_le_one (hy0 j) (hy j) (hx j))
  have hAB : A ≤ B := Finset.sum_le_sum (fun j _ => jl_g_le_one hf.le hf1 (hx j))
  have hBA : B - A ≤ (1 - f)/2 * s := by
    rw [hBdef, hAdef, hsdef, ← Finset.sum_sub_distrib, Finset.mul_sum]
    exact Finset.sum_le_sum (fun j _ => by have := jl_g_diff hf.le hf1 (hx j); linarith)
  have hA : A ≤ s * ε := by
    rw [hAdef, hsdef, Finset.sum_mul]
    exact Finset.sum_le_sum (fun j _ => jl_g_le_lin hf.le hf1 (hx j))
  have hA0 : 0 ≤ A := Finset.sum_nonneg (fun j _ => jl_g_nonneg hf.le (hx j))
  have hF6 := jl_F6 hf hf1 x hx T (by linarith)
  rw [← hsdef, ← hAdef, ← hQdef] at hF6
  have hsq : Bp^2 ≤ B^2 := pow_le_pow_left₀ hBp0 hBpB 2
  set Δ := B - A with hΔ
  have hΔ0 : 0 ≤ Δ := by linarith
  have hα : 0 ≤ (1 - f)/2 * s := mul_nonneg (by linarith) hs0
  have hAD : A * Δ ≤ (s * ε) * ((1 - f)/2 * s) := mul_le_mul hA hBA hΔ0 (by positivity)
  have hDD : Δ^2 ≤ ((1 - f)/2 * s)^2 := pow_le_pow_left₀ hΔ0 hBA 2
  have hB : B = A + Δ := by rw [hΔ]; ring
  have key : g f s - s^2 * ((1 - f)/2 * ε + ((1 - f)/2)^2/2) ≤ A + Q/2 - Bp^2/2 := by
    rw [hB] at hsq
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_left key hε0]


lemma jl_mb {x y a b A B : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hx : a ≤ x) (hx' : x ≤ A) (hy : b ≤ y)
    (hy' : y ≤ B) : a * b ≤ x * y ∧ x * y ≤ A * B :=
  ⟨mul_le_mul hx hy hb (le_trans ha hx),
    mul_le_mul hx' hy' (le_trans hb hy) (le_trans ha (le_trans hx hx'))⟩

lemma jl_E2_cs (ε u Lp D : ℝ) (ha0 : 0.3678 ≤ ε) (ha1 : ε ≤ 0.3679) (hu0 : 0.31 ≤ u)
    (hu1 : u ≤ 0.3101) (hb0 : 0.6899 ≤ Lp) (hb1 : Lp ≤ 0.69) (hd0 : 1.0032 ≤ D) (hd1 : D ≤ 1.0033) :
    (0.05:ℝ) ≤ 0.706*u - u*ε*ε*Lp*Lp/2 - u*ε - u*ε*ε
    ∧ (-0.035:ℝ) ≤ -(u*ε*Lp*Lp)/8 + u*ε*ε*Lp - (u*ε + u*ε*ε)/2 + ε*D/4 - ε*ε/2
    ∧ (-0.015:ℝ) ≤ -(u*ε*ε)/2 + u*ε*Lp/4 - (u*ε + u*ε*ε)/6 + ε*D/6 - ε*ε/3
    ∧ (-0.02:ℝ) ≤ -(u*ε)/8 - 5*(u*ε + u*ε*ε)/96 + 11*(ε*D/2 - ε*ε)/96
    ∧ (0:ℝ) ≤ 5*(ε*D/2 - ε*ε)/96 := by
  obtain ⟨e2l, e2u⟩ := jl_mb (by norm_num) (by norm_num) ha0 ha1 ha0 ha1
  obtain ⟨ul, uu⟩ := jl_mb (by norm_num) (by norm_num) hu0 hu1 ha0 ha1
  obtain ⟨uel, ueu⟩ := jl_mb (by norm_num) (by norm_num) ul uu ha0 ha1
  obtain ⟨uell, uelu⟩ := jl_mb (by norm_num) (by norm_num) uel ueu hb0 hb1
  obtain ⟨uelll, uellu⟩ := jl_mb (by norm_num) (by norm_num) uell uelu hb0 hb1
  obtain ⟨ulpl, ulpu⟩ := jl_mb (by norm_num) (by norm_num) ul uu hb0 hb1
  obtain ⟨ulppl, ulppu⟩ := jl_mb (by norm_num) (by norm_num) ulpl ulpu hb0 hb1
  obtain ⟨edl, edu⟩ := jl_mb (by norm_num) (by norm_num) ha0 ha1 hd0 hd1
  norm_num at *
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

lemma jl_E2_Q (t c0 c1 c2 c3 c4 c5 : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 0.7) (h0 : 0 ≤ c0)
    (h1 : 0.05 ≤ c1) (h2 : -0.035 ≤ c2) (h3 : -0.015 ≤ c3) (h4 : -0.02 ≤ c4) (h5 : 0 ≤ c5) :
    0 ≤ c0 + c1*t + c2*t^2 + c3*t^3 + c4*t^4 + c5*t^5 := by
  have t2 : 0 ≤ t^2 := by positivity
  have t3 : 0 ≤ t^3 := by positivity
  have t4 : 0 ≤ t^4 := by positivity
  have t5 : 0 ≤ t^5 := by positivity
  have a2 : t^2 ≤ 0.7*t := by nlinarith
  have a3 : t^3 ≤ 0.49*t := by nlinarith
  have a4 : t^4 ≤ 0.343*t := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right h1 ht0, mul_le_mul_of_nonneg_right h2 t2,
    mul_le_mul_of_nonneg_right h3 t3, mul_le_mul_of_nonneg_right h4 t4, mul_nonneg h5 t5]

lemma jl_E2_P (t ε u Lp D : ℝ) (ha0 : 0.3678 ≤ ε) (ha1 : ε ≤ 0.3679) (hu0 : 0.31 ≤ u)
    (hu1 : u ≤ 0.3101) (hb0 : 0.6899 ≤ Lp) (hb1 : Lp ≤ 0.69) (hd0 : 1.0032 ≤ D) (hd1 : D ≤ 1.0033)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 0.7) (hc0 : 0 ≤ u*(0.294 - ε*ε) - ε*D/2 + ε*ε) :
    0 ≤ u*(1 + ε - 0.706*(1 - t) - ε*(t/2*ε + t^2/8)*(Lp - t)^2)
      - (1 + t + t^2/2 + t^3/6 + t^4*(5/96)) * (u*(ε + ε*ε) + ε*(1 - t)*(D/2 - ε)) := by
  obtain ⟨c1, c2, c3, c4, c5⟩ := jl_E2_cs ε u Lp D ha0 ha1 hu0 hu1 hb0 hb1 hd0 hd1
  have hid : u*(1 + ε - 0.706*(1 - t) - ε*(t/2*ε + t^2/8)*(Lp - t)^2)
      - (1 + t + t^2/2 + t^3/6 + t^4*(5/96)) * (u*(ε + ε*ε) + ε*(1 - t)*(D/2 - ε))
      = (u*(0.294 - ε*ε) - ε*D/2 + ε*ε)
        + (0.706*u - u*ε*ε*Lp*Lp/2 - u*ε - u*ε*ε) * t
        + (-(u*ε*Lp*Lp)/8 + u*ε*ε*Lp - (u*ε + u*ε*ε)/2 + ε*D/4 - ε*ε/2) * t^2
        + (-(u*ε*ε)/2 + u*ε*Lp/4 - (u*ε + u*ε*ε)/6 + ε*D/6 - ε*ε/3) * t^3
        + (-(u*ε)/8 - 5*(u*ε + u*ε*ε)/96 + 11*(ε*D/2 - ε*ε)/96) * t^4
        + (5*(ε*D/2 - ε*ε)/96) * t^5 := by ring
  rw [hid]
  exact jl_E2_Q t _ _ _ _ _ _ ht0 ht1 hc0 c1 c2 c3 c4 c5

lemma jl_c0 (ε L D : ℝ) (hε1 : 0.3678794411 < ε) (hε2 : ε < 0.3678794416)
    (hL1 : 0.6931471803 < L) (hL2 : L < 0.6931471808) (hD0 : 0 ≤ D)
    (hD : D ≤ 1 + 1/311 + (1/311)^2/2 + (1/311)^3/6 + (1/311)^4*(5/96)) :
    (0:ℝ) ≤ (1 - (L - 1/311)) * (0.294 - ε*ε) - ε*D/2 + ε*ε := by
  have hid : (1 - (L - 1/311)) * (0.294 - ε*ε) - ε*D/2 + ε*ε
      = 0.294*(1 + 1/311) - 0.294*L + (L - 1/311)*(ε*ε) - ε*D/2 := by ring
  rw [hid]
  have e2 : (0.3678794411:ℝ)*0.3678794411 ≤ ε*ε :=
    mul_le_mul hε1.le hε1.le (by norm_num) (by linarith)
  have h1 : (0.6931471803 - 1/311:ℝ) * (0.3678794411*0.3678794411) ≤ (L - 1/311)*(ε*ε) :=
    mul_le_mul (by linarith) e2 (by norm_num) (by linarith)
  have h2 : ε*D ≤ 0.3678794416 * (1 + 1/311 + (1/311)^2/2 + (1/311)^3/6 + (1/311)^4*(5/96)) :=
    mul_le_mul hε2.le hD hD0 (by norm_num)
  norm_num at h1 h2 ⊢
  linarith

lemma jl_E2_poly (t ε L D E : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ L - 1/311) (hε1 : 0.3678794411 < ε)
    (hε2 : ε < 0.3678794416) (hL1 : 0.6931471803 < L) (hL2 : L < 0.6931471808)
    (hD0 : 1 + 1/311 ≤ D) (hD : D ≤ 1 + 1/311 + (1/311)^2/2 + (1/311)^3/6 + (1/311)^4*(5/96))
    (hE : E ≤ 1 + t + t^2/2 + t^3/6 + t^4*(5/96)) :
    0 ≤ (1 - (L - 1/311)) * (1 - E*ε + ε*(1 - E*ε - (t/2*ε + t^2/8)*((L - 1/311) - t)^2)
        - 0.706*(1 - t)) - ε*(1 - t)*(E*D/2 - E*ε) := by
  have hDn : D ≤ 1.0033 := by norm_num at hD; linarith
  have hDl : 1.0032 ≤ D := by norm_num at hD0; linarith
  have hc0 := jl_c0 ε L D hε1 hε2 hL1 hL2 (by linarith) hD
  have hP := jl_E2_P t ε (1 - (L - 1/311)) (L - 1/311) D (by linarith) (by linarith)
    (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith)
    hDl hDn ht0 (by linarith) hc0
  have hK : 0 ≤ (1 - (L - 1/311))*(ε + ε*ε) + ε*(1 - t)*(D/2 - ε) := by
    have h1 : 0 ≤ 1 - (L - 1/311) := by linarith
    have h2 : 0 ≤ ε + ε*ε := by nlinarith
    have h3 : 0 ≤ ε*(1 - t) := mul_nonneg (by linarith) (by linarith)
    have h4 : 0 ≤ D/2 - ε := by linarith
    exact add_nonneg (mul_nonneg h1 h2) (mul_nonneg h3 h4)
  have hm := mul_nonneg (sub_nonneg.mpr hE) hK
  have hid : (1 - (L - 1/311)) * (1 - E*ε + ε*(1 - E*ε - (t/2*ε + t^2/8)*((L - 1/311) - t)^2)
        - 0.706*(1 - t)) - ε*(1 - t)*(E*D/2 - E*ε)
      = ((1 - (L - 1/311))*(1 + ε - 0.706*(1 - t) - ε*(t/2*ε + t^2/8)*((L - 1/311) - t)^2)
      - (1 + t + t^2/2 + t^3/6 + t^4*(5/96)) * ((1 - (L - 1/311))*(ε + ε*ε) + ε*(1 - t)*(D/2 - ε)))
      + ((1 + t + t^2/2 + t^3/6 + t^4*(5/96)) - E)
        * ((1 - (L - 1/311))*(ε + ε*ε) + ε*(1 - t)*(D/2 - ε)) := by ring
  rw [hid]
  linarith

lemma jl_final_L (f s : ℝ) (hf : 0 < f) (hf1 : f ≤ 1) (hs0 : 0 ≤ s) (hsf : s ≤ f)
    (hgap : f - s ≤ 1 - Real.log 2 + 1/311) :
    0 ≤ 1 - Real.exp (-f) + Real.exp (-1) * (g f s - s^2 *
      ((1 - f)/2 * Real.exp (-1) + ((1 - f)/2)^2/2)) - 0.706 * f := by
  set ε := Real.exp (-1) with hεdef
  obtain ⟨hε1, hε2⟩ := jl_eps_bounds
  rw [← hεdef] at hε1 hε2
  have hε0 : 0 ≤ ε := by linarith
  have hC : 0 ≤ (1 - f)/2 * ε + ((1 - f)/2)^2/2 := by
    have : 0 ≤ (1 - f)/2 * ε := mul_nonneg (by linarith) hε0
    positivity
  have hL1 := Real.log_two_gt_d9
  have hL2 := Real.log_two_lt_d9
  have hEb : 0 ≤ 1 - Real.exp (-f) + ε * (g f f - f^2 *
      ((1 - f)/2 * ε + ((1 - f)/2)^2/2)) - 0.706 * f := by
    rw [jl_g_self]
    have := jl_E1_poly f ε (Real.exp (-f)) hf.le hf1 (by linarith) (by linarith)
      (jl_exp_neg_up6 hf.le hf1)
    linarith
  by_cases hcase : f ≤ 1 - Real.log 2 + 1/311
  · rcases hs0.eq_or_lt with h0 | h0
    · rw [← h0, jl_g_zero]
      have := jl_E3 hf.le (by norm_num at hL1 ⊢; linarith)
      nlinarith
    have ha0 : 0 ≤ 1 - Real.exp (-f) + ε * (g f 0 - 0^2 *
        ((1 - f)/2 * ε + ((1 - f)/2)^2/2)) - 0.706 * f := by
      rw [jl_g_zero]
      have := jl_E3 hf.le (by norm_num at hL1 ⊢; linarith)
      nlinarith
    exact jl_concave_ends hf.le hf h0.le hsf _ hC ε hε0 ha0 hEb
  · have hcase' : 1 - Real.log 2 + 1/311 < f := lt_of_not_ge hcase
    set L := Real.log 2 with hLdef
    have hcpos : 0 < 1 - L + 1/311 := by linarith
    have hD0 : 1 + 1/311 ≤ Real.exp (1/311) := by linarith [Real.add_one_le_exp (1/311 : ℝ)]
    have hD : Real.exp (1/311) ≤ 1 + 1/311 + (1/311)^2/2 + (1/311)^3/6 + (1/311)^4*(5/96) :=
      jl_exp_up4 (by norm_num) (by norm_num)
    have hEa : 0 ≤ 1 - Real.exp (-f) + ε * (g f (f - (1 - L + 1/311)) - (f - (1 - L + 1/311))^2 *
        ((1 - f)/2 * ε + ((1 - f)/2)^2/2)) - 0.706 * f := by
      rw [jl_g_shift f (1 - L + 1/311) hcpos.ne']
      obtain ⟨t, rfl⟩ : ∃ t, f = 1 - t := ⟨1 - f, by ring⟩
      have ht0 : 0 ≤ t := by linarith
      have htL : t ≤ L - 1/311 := by linarith
      have hexpf : Real.exp (-(1 - t)) = Real.exp t * ε := by
        rw [hεdef, ← Real.exp_add]; congr 1; ring
      have hexpa : Real.exp (-(1 - t - (1 - L + 1/311))) = Real.exp t * Real.exp (1/311) / 2 := by
        rw [show -(1 - t - (1 - L + 1/311)) = t + 1/311 - L by ring, Real.exp_sub, Real.exp_add,
          hLdef, Real.exp_log (by norm_num)]
      rw [hexpf, hexpa, show 1 - t - (1 - L + 1/311) = (L - 1/311) - t by ring]
      have hP := jl_E2_poly t ε L (Real.exp (1/311)) (Real.exp t) ht0 htL hε1 hε2 hL1 hL2 hD0 hD
        (jl_exp_up4 ht0 (by linarith))
      refine (mul_nonneg_iff_of_pos_left hcpos).mp ?_
      refine le_of_le_of_eq hP ?_
      have hinv : (1 - L + 1/311)⁻¹ * (1 - L + 1/311) = 1 := inv_mul_cancel₀ hcpos.ne'
      linear_combination (ε * (1 - t) * (Real.exp t * Real.exp (1/311) / 2 - Real.exp t * ε)) * hinv
    exact jl_concave_ends hf.le (by linarith) (by linarith) hsf _ hC ε hε0 hEa hEb

lemma jl_analytic (f : ℝ) (hf : 0 < f) (hf1 : f ≤ 1) {ι : Type*} [DecidableEq ι] (T : Finset ι)
    (x y : ι → ℝ) (hx : ∀ j, 0 ≤ x j) (hxy : ∀ j, x j ≤ y j) (hy : ∀ j, y j ≤ 1)
    (hs : ∑ j ∈ T, x j ≤ f) (hgap : f - ∑ j ∈ T, x j ≤ 1 - Real.log 2 + 1/311) :
    (0.706:ℝ) * f ≤ 1 - Real.exp (-f) + (1 / Real.exp 1) * ∑ j ∈ T, g f (x j)
      - (1 / (2 * Real.exp 1)) * (∑ j ∈ T, g (y j) (x j)) ^ 2
      + (1 / (2 * Real.exp 1)) * ∑ j ∈ T, g f (x j) ^ 2 := by
  have h1 := jl_main_lower f hf hf1 T x y hx hxy hy hs
  have h2 := jl_final_L f (∑ j ∈ T, x j) hf hf1 (Finset.sum_nonneg (fun j _ => hx j)) hs hgap
  linarith

open JailletLu MeasureTheory

/-! ### Prefix sums of a list (the left endpoints `lo`) -/

noncomputable def jlLW {β : Type*} [DecidableEq β] (w : β → ℝ) (l : List β) (b : β) : ℝ :=
  ((l.takeWhile (fun c => decide (c ≠ b))).map w).sum

lemma jlLW_cons {β : Type*} [DecidableEq β] (w : β → ℝ) (a : β) (t : List β) (b : β) :
    jlLW w (a :: t) b = if a = b then 0 else w a + jlLW w t b := by
  unfold jlLW
  by_cases h : a = b
  · subst h; simp [List.takeWhile_cons]
  · simp [List.takeWhile_cons, h]

lemma jlLW_nonneg {β : Type*} [DecidableEq β] (w : β → ℝ) (hw : ∀ c, 0 ≤ w c) :
    ∀ (l : List β) (b : β), 0 ≤ jlLW w l b := by
  intro l
  induction l with
  | nil => intro b; simp [jlLW]
  | cons a t ih =>
    intro b
    rw [jlLW_cons]
    split_ifs
    · exact le_refl _
    · exact add_nonneg (hw a) (ih b)

lemma jl_list_sum_nonneg {β : Type*} (w : β → ℝ) (hw : ∀ c, 0 ≤ w c) (l : List β) :
    0 ≤ (l.map w).sum := by
  induction l with
  | nil => simp
  | cons a t ih => simp only [List.map_cons, List.sum_cons]; exact add_nonneg (hw a) ih

lemma jlLW_le {β : Type*} [DecidableEq β] (w : β → ℝ) (hw : ∀ c, 0 ≤ w c) :
    ∀ (l : List β) (b : β), b ∈ l → jlLW w l b + w b ≤ (l.map w).sum := by
  intro l
  induction l with
  | nil => intro b hb; simp at hb
  | cons a t ih =>
    intro b hb
    rw [jlLW_cons]
    simp only [List.map_cons, List.sum_cons]
    split_ifs with h
    · subst h; have := jl_list_sum_nonneg w hw t; linarith
    · have hbt : b ∈ t := by
        rcases List.mem_cons.mp hb with e | e
        · exact absurd e.symm h
        · exact e
      have := ih b hbt
      linarith

lemma jlLW_sep {β : Type*} [DecidableEq β] (w : β → ℝ) (hw : ∀ c, 0 ≤ w c) :
    ∀ (l : List β), l.Nodup → ∀ b c, b ∈ l → c ∈ l → b ≠ c →
      jlLW w l b + w b ≤ jlLW w l c ∨ jlLW w l c + w c ≤ jlLW w l b := by
  intro l
  induction l with
  | nil => intro _ b c hb; simp at hb
  | cons a t ih =>
    intro hnd b c hb hc hbc
    have hat : a ∉ t := (List.nodup_cons.mp hnd).1
    have hnt : t.Nodup := (List.nodup_cons.mp hnd).2
    rw [jlLW_cons, jlLW_cons]
    by_cases hab : a = b
    · subst hab
      have hac : a ≠ c := hbc
      rw [if_pos rfl, if_neg hac]
      left
      have := jlLW_nonneg w hw t c
      linarith
    · by_cases hac : a = c
      · subst hac
        rw [if_neg hab, if_pos rfl]
        right
        have := jlLW_nonneg w hw t b
        linarith
      · rw [if_neg hab, if_neg hac]
        have hbt : b ∈ t := by
          rcases List.mem_cons.mp hb with e | e
          · exact absurd e.symm hab
          · exact e
        have hct : c ∈ t := by
          rcases List.mem_cons.mp hc with e | e
          · exact absurd e.symm hac
          · exact e
        rcases ih hnt b c hbt hct hbc with h | h
        · left; linarith
        · right; linarith

lemma jlLW_cover {β : Type*} [DecidableEq β] (w : β → ℝ) (hw : ∀ c, 0 ≤ w c) :
    ∀ (l : List β), l ≠ [] → l.Nodup → ∀ x : ℝ, 0 ≤ x → x ≤ (l.map w).sum →
      ∃ b ∈ l, jlLW w l b ≤ x ∧ x ≤ jlLW w l b + w b := by
  intro l
  induction l with
  | nil => intro h; exact absurd rfl h
  | cons a t ih =>
    intro _ hnd x hx0 hx1
    have hat : a ∉ t := (List.nodup_cons.mp hnd).1
    have hnt : t.Nodup := (List.nodup_cons.mp hnd).2
    simp only [List.map_cons, List.sum_cons] at hx1
    by_cases hxa : x ≤ w a
    · refine ⟨a, List.mem_cons_self .., ?_⟩
      rw [jlLW_cons, if_pos rfl]
      constructor <;> linarith
    · rw [not_le] at hxa
      by_cases ht : t = []
      · subst ht; simp at hx1; linarith
      obtain ⟨b, hbt, h1, h2⟩ := ih ht hnt (x - w a) (by linarith) (by linarith)
      have hab : a ≠ b := fun e => hat (e ▸ hbt)
      refine ⟨b, List.mem_cons_of_mem _ hbt, ?_⟩
      rw [jlLW_cons, if_neg hab]
      constructor <;> linarith

/-! ### The half rotation -/

lemma jl_rot_mem {ρ x : ℝ} (hx : x ∈ Set.Icc 0 ρ) : rot ρ x ∈ Set.Icc 0 ρ := by
  obtain ⟨h0, h1⟩ := hx
  unfold rot
  split_ifs with h
  · constructor <;> linarith
  · rw [not_lt] at h; constructor <;> linarith

lemma jl_rot_meas (ρ : ℝ) : Measurable (rot ρ) := by
  unfold rot
  exact Measurable.ite (measurableSet_Iio : MeasurableSet {x : ℝ | x < ρ / 2})
    (measurable_id.add_const _) (measurable_id.sub_const _)

lemma jl_rot_fiber (ρ p : ℝ) :
    {x : ℝ | rot ρ x = p} ⊆ ({p - ρ / 2, p + ρ / 2} : Set ℝ) := by
  intro x hx
  simp only [Set.mem_setOf_eq] at hx
  unfold rot at hx
  split_ifs at hx
  · left; linarith
  · right; simp; linarith

/-- The symmetry of the list numbers: the half rotation is measure preserving and an involution. -/
lemma jl_rot_symm_le (ρ : ℝ) (B C : Set ℝ) :
    volume {x : ℝ | x ∈ Set.Icc 0 ρ ∧ x ∈ B ∧ rot ρ x ∈ C}
      ≤ volume {x : ℝ | x ∈ Set.Icc 0 ρ ∧ x ∈ C ∧ rot ρ x ∈ B} := by
  set T := {x : ℝ | x ∈ Set.Icc 0 ρ ∧ x ∈ C ∧ rot ρ x ∈ B} with hT
  have hsub : {x : ℝ | x ∈ Set.Icc 0 ρ ∧ x ∈ B ∧ rot ρ x ∈ C}
      ⊆ ((fun x => x + ρ / 2) ⁻¹' (T ∩ Set.Ici (ρ / 2)))
        ∪ ((fun x => x + (-(ρ / 2))) ⁻¹' ((T \ Set.Ici (ρ / 2)) ∪ {ρ / 2})) := by
    rintro x ⟨⟨h0, h1⟩, hB, hC⟩
    by_cases hx : x < ρ / 2
    · left
      have hr : rot ρ x = x + ρ / 2 := by unfold rot; rw [if_pos hx]
      rw [hr] at hC
      have hr2 : rot ρ (x + ρ / 2) = x := by
        unfold rot; rw [if_neg (by linarith)]; ring
      refine ⟨⟨⟨by linarith, by linarith⟩, hC, by rw [hr2]; exact hB⟩, ?_⟩
      show ρ / 2 ≤ x + ρ / 2
      linarith
    · right
      rw [not_lt] at hx
      have hr : rot ρ x = x - ρ / 2 := by unfold rot; rw [if_neg (by linarith)]
      rw [hr] at hC
      show x + -(ρ / 2) ∈ (T \ Set.Ici (ρ / 2)) ∪ {ρ / 2}
      by_cases he : x + -(ρ / 2) < ρ / 2
      · left
        have hr2 : rot ρ (x + -(ρ / 2)) = x := by
          unfold rot; rw [if_pos he]; ring
        refine ⟨⟨⟨by linarith, by linarith⟩, by rw [show x + -(ρ / 2) = x - ρ / 2 by ring]; exact hC,
          by rw [hr2]; exact hB⟩, ?_⟩
        show ¬ (ρ / 2 ≤ x + -(ρ / 2))
        linarith
      · right
        show x + -(ρ / 2) = ρ / 2
        linarith
  calc volume {x : ℝ | x ∈ Set.Icc 0 ρ ∧ x ∈ B ∧ rot ρ x ∈ C}
      ≤ volume (((fun x => x + ρ / 2) ⁻¹' (T ∩ Set.Ici (ρ / 2)))
        ∪ ((fun x => x + (-(ρ / 2))) ⁻¹' ((T \ Set.Ici (ρ / 2)) ∪ {ρ / 2}))) := measure_mono hsub
    _ ≤ volume ((fun x => x + ρ / 2) ⁻¹' (T ∩ Set.Ici (ρ / 2)))
        + volume ((fun x => x + (-(ρ / 2))) ⁻¹' ((T \ Set.Ici (ρ / 2)) ∪ {ρ / 2})) :=
          measure_union_le _ _
    _ = volume (T ∩ Set.Ici (ρ / 2)) + volume ((T \ Set.Ici (ρ / 2)) ∪ {ρ / 2}) := by
          rw [measure_preimage_add_right, measure_preimage_add_right]
    _ ≤ volume (T ∩ Set.Ici (ρ / 2)) + (volume (T \ Set.Ici (ρ / 2)) + volume ({ρ / 2} : Set ℝ)) := by
          gcongr; exact measure_union_le _ _
    _ = volume T := by
          rw [Real.volume_singleton, add_zero, measure_inter_add_diff _ measurableSet_Ici]

lemma jl_rot_symm (ρ : ℝ) (B C : Set ℝ) :
    volume {x : ℝ | x ∈ Set.Icc 0 ρ ∧ x ∈ B ∧ rot ρ x ∈ C}
      = volume {x : ℝ | x ∈ Set.Icc 0 ρ ∧ x ∈ C ∧ rot ρ x ∈ B} :=
  le_antisymm (jl_rot_symm_le ρ B C) (jl_rot_symm_le ρ C B)

lemma jl_S_meas (ρ : ℝ) {B C : Set ℝ} (hB : MeasurableSet B) (hC : MeasurableSet C) :
    MeasurableSet {x : ℝ | x ∈ Set.Icc 0 ρ ∧ x ∈ B ∧ rot ρ x ∈ C} :=
  measurableSet_Icc.inter (hB.inter (jl_rot_meas ρ hC))

lemma jl_S_fin (ρ : ℝ) (B C : Set ℝ) :
    volume {x : ℝ | x ∈ Set.Icc 0 ρ ∧ x ∈ B ∧ rot ρ x ∈ C} ≠ ⊤ := by
  refine ne_top_of_le_ne_top (b := volume (Set.Icc (0:ℝ) ρ)) ?_ (measure_mono (fun x hx => hx.1))
  rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top

/-- Self overlap of an interval with its half rotation. -/
lemma jl_self_overlap (ρ l w : ℝ) :
    (volume {x : ℝ | x ∈ Set.Icc 0 ρ ∧ x ∈ Set.Icc l (l + w) ∧ rot ρ x ∈ Set.Icc l (l + w)}).toReal
      ≤ max (2 * w - ρ) 0 := by
  have hsub : {x : ℝ | x ∈ Set.Icc 0 ρ ∧ x ∈ Set.Icc l (l + w) ∧ rot ρ x ∈ Set.Icc l (l + w)}
      ⊆ Set.Icc l (l + w - ρ / 2) ∪ Set.Icc (l + ρ / 2) (l + w) := by
    rintro x ⟨_, ⟨h1, h2⟩, h3, h4⟩
    unfold rot at h3 h4
    split_ifs at h3 h4 with h
    · left; constructor <;> linarith
    · right; constructor <;> linarith
  have hle := (measure_mono (μ := volume) hsub).trans (measure_union_le _ _)
  rw [Real.volume_Icc, Real.volume_Icc] at hle
  have hfin : ENNReal.ofReal (l + w - ρ / 2 - l) + ENNReal.ofReal (l + w - (l + ρ / 2)) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩
  have h1 := ENNReal.toReal_mono hfin hle
  rw [ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal', ENNReal.toReal_ofReal'] at h1
  have e1 : l + w - ρ / 2 - l = w - ρ / 2 := by ring
  have e2 : l + w - (l + ρ / 2) = w - ρ / 2 := by ring
  rw [e1, e2] at h1
  rcases le_total (w - ρ / 2) 0 with h | h
  · rw [max_eq_right h] at h1
    have : (0:ℝ) ≤ max (2 * w - ρ) 0 := le_max_right _ _
    linarith
  · rw [max_eq_left h] at h1
    have : 2 * w - ρ ≤ max (2 * w - ρ) 0 := le_max_left _ _
    linarith

/-! ### The intervals `J` for a feasible flow and an admissible order -/

section Tiling
variable {A I : Type*} [Fintype A] [Fintype I] [DecidableEq A]

lemma jl_fA_nonneg {E : Set (A × I)} {r : I → ℝ} {n : ℕ} {f : A → I → ℝ}
    (hf : LP4Feasible E r n f) (i : I) (b : Option A) : 0 ≤ fA r f b i := by
  cases b with
  | none => show 0 ≤ r i - ∑ a, f a i; linarith [hf.2.2.2.1 i]
  | some a => exact hf.1 a i

lemma jl_lo_eq (r : I → ℝ) (f : A → I → ℝ) (ord : I → List (Option A)) (i : I) (b : Option A) :
    lo r f ord i b = jlLW (fun c => fA r f c i) (ord i) b := rfl

lemma jl_sum_ord {E : Set (A × I)} {r : I → ℝ} {n : ℕ} {f : A → I → ℝ}
    (hf : LP4Feasible E r n f) {ord : I → List (Option A)} (hord : IsAdmissibleOrder E ord) (i : I) :
    ((ord i).map (fun c => fA r f c i)).sum = r i := by
  rw [← List.sum_toFinset _ (hord i).1]
  have h1 : ∑ b ∈ (ord i).toFinset, fA r f b i
      = ∑ b : Option A, if b ∈ (ord i).toFinset then fA r f b i else 0 := by
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  rw [h1, Fintype.sum_option]
  have hnone : (none : Option A) ∈ (ord i).toFinset := by
    rw [List.mem_toFinset]; exact ((hord i).2 none).2 (Or.inl rfl)
  rw [if_pos hnone]
  have h2 : ∀ a : A, (if (some a) ∈ (ord i).toFinset then fA r f (some a) i else 0) = f a i := by
    intro a
    split_ifs with h
    · rfl
    · rw [List.mem_toFinset] at h
      have : (a, i) ∉ E := fun hE => h (((hord i).2 (some a)).2 (Or.inr ⟨a, rfl, hE⟩))
      exact (hf.2.1 a i this).symm
  simp only [h2]
  show r i - ∑ a, f a i + ∑ a, f a i = r i
  ring

lemma jl_J_sub {E : Set (A × I)} {r : I → ℝ} {n : ℕ} {f : A → I → ℝ}
    (hf : LP4Feasible E r n f) {ord : I → List (Option A)} (hord : IsAdmissibleOrder E ord)
    (i : I) (b : Option A) : J r f ord i b ⊆ Set.Icc 0 (r i) := by
  unfold J
  split_ifs with hb
  · intro x ⟨h1, h2⟩
    have hw := jl_fA_nonneg hf i
    have l0 := jlLW_nonneg _ hw (ord i) b
    have l1 := jlLW_le _ hw (ord i) b hb
    rw [jl_sum_ord hf hord i] at l1
    rw [jl_lo_eq] at h1 h2
    constructor <;> linarith
  · exact Set.empty_subset _

lemma jl_J_meas (r : I → ℝ) (f : A → I → ℝ) (ord : I → List (Option A)) (i : I) (b : Option A) :
    MeasurableSet (J r f ord i b) := by
  unfold J
  split_ifs
  · exact measurableSet_Icc
  · exact MeasurableSet.empty

lemma jl_J_cover {E : Set (A × I)} {r : I → ℝ} {n : ℕ} {f : A → I → ℝ}
    (hf : LP4Feasible E r n f) {ord : I → List (Option A)} (hord : IsAdmissibleOrder E ord)
    (i : I) (x : ℝ) (hx : x ∈ Set.Icc 0 (r i)) : ∃ b, x ∈ J r f ord i b := by
  have hw := jl_fA_nonneg hf i
  have hne : ord i ≠ [] := by
    intro h
    have := ((hord i).2 none).2 (Or.inl rfl)
    rw [h] at this; simp at this
  obtain ⟨b, hb, h1, h2⟩ := jlLW_cover _ hw (ord i) hne (hord i).1 x hx.1
    (by rw [jl_sum_ord hf hord i]; exact hx.2)
  refine ⟨b, ?_⟩
  unfold J
  rw [if_pos hb, jl_lo_eq]
  exact ⟨h1, h2⟩

lemma jl_J_inter {E : Set (A × I)} {r : I → ℝ} {n : ℕ} {f : A → I → ℝ}
    (hf : LP4Feasible E r n f) {ord : I → List (Option A)} (hord : IsAdmissibleOrder E ord)
    (i : I) (b c : Option A) (hbc : b ≠ c) :
    ∃ p, J r f ord i b ∩ J r f ord i c ⊆ {p} := by
  have hw := jl_fA_nonneg hf i
  unfold J
  by_cases hb : b ∈ ord i
  · by_cases hc : c ∈ ord i
    · rw [if_pos hb, if_pos hc, jl_lo_eq, jl_lo_eq]
      rcases jlLW_sep _ hw (ord i) (hord i).1 b c hb hc hbc with h | h
      · refine ⟨jlLW (fun c => fA r f c i) (ord i) c, ?_⟩
        rintro x ⟨⟨_, h2⟩, ⟨h3, _⟩⟩
        show x = _
        linarith
      · refine ⟨jlLW (fun c => fA r f c i) (ord i) b, ?_⟩
        rintro x ⟨⟨h1, _⟩, ⟨_, h4⟩⟩
        show x = _
        linarith
    · rw [if_neg hc]; exact ⟨0, by simp⟩
  · rw [if_neg hb]; exact ⟨0, by simp⟩

/-! ### Row sums of the list numbers -/

lemma jl_mi_symm (r : I → ℝ) (f : A → I → ℝ) (ord : I → List (Option A)) (i : I) (b c : Option A) :
    mi r f ord i b c = mi r f ord i c b := by
  unfold mi
  rw [jl_rot_symm]

lemma jl_mi_le {E : Set (A × I)} {r : I → ℝ} {n : ℕ} {f : A → I → ℝ}
    (hf : LP4Feasible E r n f) (ord : I → List (Option A)) (i : I) (b c : Option A) :
    mi r f ord i b c ≤ fA r f b i := by
  have hw := jl_fA_nonneg hf i b
  unfold mi
  by_cases hb : b ∈ ord i
  · have hsub : {x : ℝ | x ∈ Set.Icc 0 (r i) ∧ x ∈ J r f ord i b ∧ rot (r i) x ∈ J r f ord i c}
        ⊆ Set.Icc (lo r f ord i b) (lo r f ord i b + fA r f b i) := fun x hx => by
      have h := hx.2.1
      unfold J at h
      rw [if_pos hb] at h
      exact h
    have hle := measure_mono (μ := volume) hsub
    rw [Real.volume_Icc] at hle
    have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
    rw [ENNReal.toReal_ofReal (by linarith)] at h2
    linarith
  · have hsub : {x : ℝ | x ∈ Set.Icc 0 (r i) ∧ x ∈ J r f ord i b ∧ rot (r i) x ∈ J r f ord i c}
        ⊆ ∅ := fun x hx => by
      have h := hx.2.1
      unfold J at h
      rw [if_neg hb] at h
      exact h
    rw [Set.subset_empty_iff.mp hsub, measure_empty, ENNReal.toReal_zero]
    exact hw

lemma jl_row_sum {E : Set (A × I)} {r : I → ℝ} {n : ℕ} {f : A → I → ℝ}
    (hf : LP4Feasible E r n f) {ord : I → List (Option A)} (hord : IsAdmissibleOrder E ord)
    (i : I) (a : A) : ∑ c : Option A, mi r f ord i (some a) c = f a i := by
  set S := fun c : Option A =>
    {x : ℝ | x ∈ Set.Icc 0 (r i) ∧ x ∈ J r f ord i (some a) ∧ rot (r i) x ∈ J r f ord i c} with hS
  have hfin : ∀ c, volume (S c) ≠ ⊤ := fun c => jl_S_fin _ _ _
  have hmi : ∀ c, mi r f ord i (some a) c = (volume (S c)).toReal := fun c => rfl
  simp only [hmi]
  rw [← ENNReal.toReal_sum (fun c _ => hfin c)]
  -- the union of the pieces is J(some a)
  have hdisj : (↑(Finset.univ : Finset (Option A)) : Set (Option A)).Pairwise (Function.onFun (AEDisjoint volume) S) := by
    intro c _ c' _ hcc'
    obtain ⟨p, hp⟩ := jl_J_inter hf hord i c c' hcc'
    show volume (S c ∩ S c') = 0
    have hsub : S c ∩ S c' ⊆ ({p - r i / 2, p + r i / 2} : Set ℝ) := by
      rintro x ⟨⟨_, _, h1⟩, ⟨_, _, h2⟩⟩
      exact jl_rot_fiber (r i) p (hp ⟨h1, h2⟩)
    exact measure_mono_null hsub ((Set.toFinite _).measure_zero _)
  have hmeas : ∀ c ∈ (Finset.univ : Finset (Option A)), NullMeasurableSet (S c) volume :=
    fun c _ => (jl_S_meas _ (jl_J_meas r f ord i _) (jl_J_meas r f ord i c)).nullMeasurableSet
  rw [← measure_biUnion_finset₀ hdisj hmeas]
  have hU : (⋃ c ∈ (Finset.univ : Finset (Option A)), S c) = J r f ord i (some a) := by
    ext x
    simp only [Finset.mem_univ, Set.iUnion_true, Set.mem_iUnion, hS, Set.mem_setOf_eq]
    constructor
    · rintro ⟨c, _, h, _⟩; exact h
    · intro hx
      have hx0 := jl_J_sub hf hord i (some a) hx
      obtain ⟨c, hc⟩ := jl_J_cover hf hord i (rot (r i) x) (jl_rot_mem hx0)
      exact ⟨c, hx0, hx, hc⟩
  rw [hU]
  unfold J
  split_ifs with ha
  · rw [Real.volume_Icc, ENNReal.toReal_ofReal (by have := hf.1 a i; show 0 ≤ _ + f a i - _; linarith)]
    show _ + f a i - _ = f a i
    ring
  · have : (a, i) ∉ E := fun hE => ha (((hord i).2 (some a)).2 (Or.inr ⟨a, rfl, hE⟩))
    rw [measure_empty, ENNReal.toReal_zero, hf.2.1 a i this]

lemma jl_mi_self {E : Set (A × I)} {r : I → ℝ} {n : ℕ} {f : A → I → ℝ}
    (hf : LP4Feasible E r n f) (ord : I → List (Option A)) (i : I) (a : A) :
    mi r f ord i (some a) (some a) ≤ max (2 * f a i - r i) 0 := by
  unfold mi J
  split_ifs with ha
  · exact jl_self_overlap (r i) _ _
  · simp only [Set.mem_empty_iff_false, false_and, and_false, Set.setOf_false, measure_empty,
      ENNReal.toReal_zero]
    exact le_max_right _ _

end Tiling

section Main
variable {A I : Type*} [Fintype A] [Fintype I] [DecidableEq A]

lemma jl_sum_Astar {E : Set (A × I)} {r : I → ℝ} {n : ℕ} {f : A → I → ℝ}
    (hf : LP4Feasible E r n f) {ord : I → List (Option A)} (hord : IsAdmissibleOrder E ord) (a : A) :
    ∑ b ∈ Astar a, m r f ord (some a) b = fTot f a - ∑ i, mi r f ord i (some a) (some a) := by
  unfold Astar m fTot
  rw [Finset.sum_comm]
  have h : ∀ i, ∑ b ∈ Finset.univ.erase (some a), mi r f ord i (some a) b
      = f a i - mi r f ord i (some a) (some a) := by
    intro i
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ _), jl_row_sum hf hord i a]
  rw [Finset.sum_congr rfl (fun i _ => h i), Finset.sum_sub_distrib]

lemma jl_main (E : Set (A × I)) (r : I → ℝ) (n : ℕ) (f : A → I → ℝ)
    (hf : LP4Feasible E r n f) (ord : I → List (Option A)) (hord : IsAdmissibleOrder E ord)
    (hn : 311 ≤ n) (a : A) (hFpos : 0 < fTot f a) :
    (0.706 : ℝ) ≤ third r f ord a / fTot f a := by
  have hF1 : fTot f a ≤ 1 := hf.2.2.1 a
  have hmi0 : ∀ i b c, 0 ≤ mi r f ord i b c := fun _ _ _ => ENNReal.toReal_nonneg
  have hx0 : ∀ b, 0 ≤ m r f ord (some a) b := fun b => Finset.sum_nonneg (fun i _ => hmi0 i _ _)
  have hself0 : 0 ≤ ∑ i, mi r f ord i (some a) (some a) :=
    Finset.sum_nonneg (fun i _ => hmi0 i _ _)
  have hsum := jl_sum_Astar hf hord a
  have hs : ∑ b ∈ Astar a, m r f ord (some a) b ≤ fTot f a := by rw [hsum]; linarith
  have hselfle : ∑ i, mi r f ord i (some a) (some a) ≤ 1 - Real.log 2 + 1/311 := by
    have h1 : ∑ i, mi r f ord i (some a) (some a) ≤ ∑ i, max (2 * f a i - r i) 0 :=
      Finset.sum_le_sum (fun i _ => jl_mi_self hf ord i a)
    have h2 := hf.2.2.2.2 a
    have h3 : (311:ℝ) ≤ n := by exact_mod_cast hn
    have h4 : 1 / (n:ℝ) ≤ 1/311 := one_div_le_one_div_of_le (by norm_num) h3
    linarith
  have hgap : fTot f a - ∑ b ∈ Astar a, m r f ord (some a) b ≤ 1 - Real.log 2 + 1/311 := by
    rw [hsum]; linarith
  have hy : ∀ b, fStar f b ≤ 1 := by
    intro b
    cases b with
    | none => exact le_refl _
    | some b0 => exact hf.2.2.1 b0
  have hxy : ∀ b, m r f ord (some a) b ≤ fStar f b := by
    intro b
    cases b with
    | none =>
      have hmem : (none : Option A) ∈ Astar a := by unfold Astar; simp
      have h1 : m r f ord (some a) none ≤ ∑ c ∈ Astar a, m r f ord (some a) c :=
        Finset.single_le_sum (fun c _ => hx0 c) hmem
      show m r f ord (some a) none ≤ 1
      linarith
    | some b0 =>
      show ∑ i, mi r f ord i (some a) (some b0) ≤ ∑ i, f b0 i
      exact Finset.sum_le_sum (fun i _ => by
        rw [jl_mi_symm]; exact jl_mi_le hf ord i (some b0) (some a))
  have hB : ∑ b ∈ Astar a, g (fStar f b) (m r f ord b (some a))
      = ∑ b ∈ Astar a, g (fStar f b) (m r f ord (some a) b) := by
    refine Finset.sum_congr rfl (fun b _ => ?_)
    congr 1
    exact Finset.sum_congr rfl (fun i _ => jl_mi_symm r f ord i b (some a))
  have key := jl_analytic (fTot f a) hFpos hF1 (Astar a) (fun b => m r f ord (some a) b)
    (fStar f) hx0 hxy hy hs hgap
  rw [le_div_iff₀ hFpos]
  unfold third
  rw [hB]
  exact key

end Main

open JailletLu in
theorem solution {A I : Type*} [Fintype A] [Fintype I] [DecidableEq A]
    (E : Set (A × I)) (r : I → ℝ) (hr : ∀ i, r i ≤ 1) (n : ℕ) (f : A → I → ℝ)
    (hf : LP4Feasible E r n f) (ord : I → List (Option A)) (hord : IsAdmissibleOrder E ord) (hn : 311 ≤ n) :
    ∀ a : A, 0 < fTot f a → (0.706 : ℝ) ≤ third r f ord a / fTot f a := by
  intro a ha
  exact jl_main E r n f hf ord hord hn a ha
