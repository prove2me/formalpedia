-- Prove2me | solution 1 for Kyprianou.Ch01.stableGammaIntegralByParts
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-15T21:26:22.249915+00:00
-- url     : https://prove2.me/submissions/a217dd8c-3be5-4fd3-b361-8dcc1c2441c9

import Mathlib
open MeasureTheory Set Real Filter Topology
set_option autoImplicit false

theorem KypSGIBP_env (alpha u : ℝ) (ha0 : 0 < alpha) (ha1 : alpha < 1) :
    IntegrableOn (fun x : ℝ =>
      if x ≤ 1 then u * x ^ (-alpha) else x ^ (-alpha - 1))
      (Set.Ioi (0 : ℝ)) := by
  have hsplit : Set.Ioi (0:ℝ) = Set.Ioc 0 1 ∪ Set.Ioi 1 := by
    ext x; simp only [mem_Ioi, mem_union, mem_Ioc]
    constructor
    · intro hx; by_cases h : x ≤ 1
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr (lt_of_not_ge h)
    · rintro (⟨h1, _⟩ | h2) <;> linarith
  rw [hsplit]
  apply IntegrableOn.union
  · have h1 : IntegrableOn (fun x : ℝ => u * x ^ (-alpha)) (Set.Ioc 0 1) := by
      have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1)
        (r := -alpha) (by linarith)).const_mul u
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)] at this
      exact this
    refine h1.congr_fun (fun x hx => ?_) measurableSet_Ioc
    simp [hx.2]
  · have h2 : IntegrableOn (fun x : ℝ => x ^ (-alpha - 1)) (Set.Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num)
    refine h2.congr_fun (fun x hx => ?_) measurableSet_Ioi
    have : ¬ x ≤ 1 := not_le.mpr hx
    simp [this]

theorem solution
    (alpha u : ℝ) (ha0 : 0 < alpha) (ha1 : alpha < 1) (hu : 0 < u) :
    IntegrableOn (fun x : ℝ =>
      (Real.exp (-(u * x)) - 1) * x ^ (-alpha - 1))
      (Set.Ioi (0 : ℝ)) ∧
    (∫ x in Set.Ioi (0 : ℝ),
      (Real.exp (-(u * x)) - 1) * x ^ (-alpha - 1) ∂volume) =
    -(u / alpha) * (∫ x in Set.Ioi (0 : ℝ),
      Real.exp (-(u * x)) * x ^ (-alpha) ∂volume) := by
  set env := fun x : ℝ => if x ≤ 1 then u * x ^ (-alpha) else x ^ (-alpha - 1) with henv
  have hEnv : IntegrableOn env (Ioi 0) := KypSGIBP_env alpha u ha0 ha1
  -- basic pointwise facts
  have hpow : ∀ x : ℝ, 0 < x → x ^ (-alpha - 1) = x ^ (-alpha) / x := by
    intro x hx
    rw [show -alpha - 1 = -alpha - 1 from rfl, Real.rpow_sub_one hx.ne']
  have hf_le : ∀ x : ℝ, 0 < x → |Real.exp (-(u * x)) - 1| ≤ u * x := by
    intro x hx
    have h1 := Real.add_one_le_exp (-(u * x))
    have h2 : Real.exp (-(u * x)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith
    rw [abs_of_nonpos (by linarith)]; linarith
  have hf_le1 : ∀ x : ℝ, 0 < x → |Real.exp (-(u * x)) - 1| ≤ 1 := by
    intro x hx
    have h0 := Real.exp_pos (-(u * x))
    have h2 : Real.exp (-(u * x)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith
    rw [abs_of_nonpos (by linarith)]; linarith
  have hcont1 : ContinuousOn (fun x : ℝ => (Real.exp (-(u * x)) - 1) * x ^ (-alpha - 1)) (Ioi 0) := by
    apply ContinuousOn.mul
    · fun_prop
    · exact fun x hx => (Real.continuousAt_rpow_const x _ (Or.inl (ne_of_gt hx))).continuousWithinAt
  have hcont2 : ContinuousOn (fun x : ℝ => Real.exp (-(u * x)) * x ^ (-alpha)) (Ioi 0) := by
    apply ContinuousOn.mul
    · fun_prop
    · exact fun x hx => (Real.continuousAt_rpow_const x _ (Or.inl (ne_of_gt hx))).continuousWithinAt
  have hI1 : IntegrableOn (fun x : ℝ => (Real.exp (-(u * x)) - 1) * x ^ (-alpha - 1)) (Ioi 0) := by
    refine Integrable.mono' hEnv (hcont1.aestronglyMeasurable measurableSet_Ioi) ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall (fun x hx => ?_)
    have hx : 0 < x := hx
    have hp := Real.rpow_pos_of_pos hx (-alpha)
    have hp1 := Real.rpow_pos_of_pos hx (-alpha - 1)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hp1, henv]
    dsimp only
    split_ifs with h
    · calc |Real.exp (-(u * x)) - 1| * x ^ (-alpha - 1) ≤ (u * x) * x ^ (-alpha - 1) :=
            mul_le_mul_of_nonneg_right (hf_le x hx) hp1.le
        _ = u * x ^ (-alpha) := by rw [hpow x hx]; field_simp
    · calc |Real.exp (-(u * x)) - 1| * x ^ (-alpha - 1) ≤ 1 * x ^ (-alpha - 1) :=
            mul_le_mul_of_nonneg_right (hf_le1 x hx) hp1.le
        _ = x ^ (-alpha - 1) := one_mul _
  have hI2 : IntegrableOn (fun x : ℝ => Real.exp (-(u * x)) * x ^ (-alpha)) (Ioi 0) := by
    refine Integrable.mono' (hEnv.const_mul (1 / u)) (hcont2.aestronglyMeasurable measurableSet_Ioi) ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall (fun x hx => ?_)
    have hx : 0 < x := hx
    have hp := Real.rpow_pos_of_pos hx (-alpha)
    have he := Real.exp_pos (-(u * x))
    rw [Real.norm_eq_abs, abs_of_pos (mul_pos he hp), henv]
    dsimp only
    have he1 : Real.exp (-(u * x)) ≤ 1 := by rw [Real.exp_le_one_iff]; nlinarith
    split_ifs with h
    · rw [show 1 / u * (u * x ^ (-alpha)) = x ^ (-alpha) by field_simp]
      nlinarith
    · -- u x e^{-ux} ≤ 1
      have hk : u * x * Real.exp (-(u * x)) ≤ 1 := by
        have h1 := Real.add_one_le_exp (u * x)
        have h2 : Real.exp (u * x) * Real.exp (-(u * x)) = 1 := by
          rw [← Real.exp_add]; simp
        nlinarith
      rw [hpow x hx]
      rw [show 1 / u * (x ^ (-alpha) / x) = x ^ (-alpha) / (u * x) by field_simp]
      rw [le_div_iff₀ (by positivity)]
      nlinarith
  refine ⟨hI1, ?_⟩
  -- integration by parts
  have hderf : ∀ x ∈ Ioi (0:ℝ), HasDerivAt (fun x => Real.exp (-(u * x)) - 1)
      (-u * Real.exp (-(u * x))) x := by
    intro x _
    have h1 : HasDerivAt (fun x : ℝ => -(u * x)) (-u) x := by
      have := ((hasDerivAt_id x).const_mul u).neg
      simp only [mul_one] at this
      exact this
    exact (h1.exp.sub_const 1).congr_deriv (by ring)
  have hderg : ∀ x ∈ Ioi (0:ℝ), HasDerivAt (fun x : ℝ => -(x ^ (-alpha)) / alpha)
      (x ^ (-alpha - 1)) x := by
    intro x hx
    have := ((Real.hasDerivAt_rpow_const (p := -alpha) (Or.inl (ne_of_gt (show (0:ℝ) < x from hx)))).neg).div_const alpha
    exact this.congr_deriv (by rw [neg_mul, neg_neg, mul_div_right_comm, div_self ha0.ne', one_mul])
  have hfg_eq : ∀ x : ℝ, (-u * Real.exp (-(u * x))) * (-(x ^ (-alpha)) / alpha)
      = (u / alpha) * (Real.exp (-(u * x)) * x ^ (-alpha)) := by
    intro x; field_simp
  have hI3 : IntegrableOn ((fun x => -u * Real.exp (-(u * x))) * fun x : ℝ => -(x ^ (-alpha)) / alpha) (Ioi 0) := by
    have : IntegrableOn (fun x : ℝ => (u / alpha) * (Real.exp (-(u * x)) * x ^ (-alpha))) (Ioi 0) :=
      hI2.const_mul (u / alpha)
    refine IntegrableOn.congr_fun this (fun x _ => ?_) measurableSet_Ioi
    simp only [Pi.mul_apply]; rw [hfg_eq]
  have hI1' : IntegrableOn ((fun x => Real.exp (-(u * x)) - 1) * fun x : ℝ => x ^ (-alpha - 1)) (Ioi 0) := hI1
  have hzero : Tendsto ((fun x => Real.exp (-(u * x)) - 1) * fun x : ℝ => -(x ^ (-alpha)) / alpha)
      (𝓝[>] 0) (𝓝 0) := by
    have hlim : Tendsto (fun x : ℝ => (u / alpha) * x ^ (1 - alpha)) (𝓝[>] 0) (𝓝 0) := by
      have hc := Real.continuousAt_rpow_const 0 (1 - alpha) (Or.inr (by linarith))
      have : Tendsto (fun x : ℝ => x ^ (1 - alpha)) (𝓝 0) (𝓝 0) := by
        have := hc.tendsto
        rwa [Real.zero_rpow (by linarith)] at this
      have := (this.const_mul (u / alpha)).mono_left (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))
      simpa using this
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx : 0 < x := hx
    have hp := Real.rpow_pos_of_pos hx (-alpha)
    simp only [Pi.mul_apply, Real.norm_eq_abs, abs_mul, abs_div, abs_neg, abs_of_pos hp,
      abs_of_pos ha0]
    calc |Real.exp (-(u * x)) - 1| * (x ^ (-alpha) / alpha) ≤ (u * x) * (x ^ (-alpha) / alpha) :=
          mul_le_mul_of_nonneg_right (hf_le x hx) (by positivity)
      _ = (u / alpha) * x ^ (1 - alpha) := by
          rw [show (1 - alpha) = -alpha + 1 by ring, Real.rpow_add_one hx.ne']
          field_simp
  have hinf : Tendsto ((fun x => Real.exp (-(u * x)) - 1) * fun x : ℝ => -(x ^ (-alpha)) / alpha)
      atTop (𝓝 0) := by
    have hlim : Tendsto (fun x : ℝ => x ^ (-alpha) / alpha) atTop (𝓝 0) := by
      simpa using (tendsto_rpow_neg_atTop ha0).div_const alpha
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_gt_atTop 0] with x hx
    have hp := Real.rpow_pos_of_pos hx (-alpha)
    simp only [Pi.mul_apply, Real.norm_eq_abs, abs_mul, abs_div, abs_neg, abs_of_pos hp,
      abs_of_pos ha0]
    calc |Real.exp (-(u * x)) - 1| * (x ^ (-alpha) / alpha) ≤ 1 * (x ^ (-alpha) / alpha) :=
          mul_le_mul_of_nonneg_right (hf_le1 x hx) (by positivity)
      _ = x ^ (-alpha) / alpha := one_mul _
  have hibp := integral_Ioi_mul_deriv_eq_deriv_mul hderf hderg hI1' hI3 hzero hinf
  rw [hibp]
  simp only [hfg_eq]
  rw [integral_const_mul]
  ring
