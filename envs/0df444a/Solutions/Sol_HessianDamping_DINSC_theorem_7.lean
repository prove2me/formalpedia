-- Prove2me | solution 1 for HessianDamping.DINSC.theorem_7
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T03:40:51.338286+00:00
-- url     : https://prove2.me/submissions/fe5c9788-952d-4e14-9af9-7d56d2949997

import Mathlib
import Definitions.Def_HessianDamping_DINSC_Setting

set_option autoImplicit false

namespace HD7Aux

open Set Filter Topology MeasureTheory InnerProductSpace

/-- The Riesz map `StrongDual ℝ H → H` as a real continuous linear map. -/
noncomputable def gradL (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] : StrongDual ℝ H →L[ℝ] H where
  toFun φ := (toDual ℝ H).symm φ
  map_add' a b := map_add _ a b
  map_smul' c a := by simp
  cont := (toDual ℝ H).symm.continuous

theorem gradient_eq_gradL {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (f : H → ℝ) : gradient f = fun y => gradL H (fderiv ℝ f y) := rfl

theorem contDiff_one_gradient {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (f : H → ℝ) (hf : ContDiff ℝ 2 f) : ContDiff ℝ 1 (gradient f) := by
  rw [gradient_eq_gradL]
  exact (gradL H).contDiff.comp (hf.fderiv_right (by norm_num))

/-- First-order inequality for a differentiable `μ`-strongly convex function. -/
theorem sc_first_order {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (f : H → ℝ) (hfd : Differentiable ℝ f) (μ : ℝ)
    (hsc : HessianDamping.DINSC.IsStronglyConvex f μ) (y z : H) :
    f y + inner ℝ (gradient f y) (z - y) + μ / 2 * ‖z - y‖ ^ 2 ≤ f z := by
  have h0 : ConvexOn ℝ univ (fun x => f x - μ / 2 * ‖x‖ ^ 2) := hsc
  have hconv : ConvexOn ℝ univ ((fun x => f x - μ / 2 * ‖x‖ ^ 2) ∘ (AffineMap.lineMap y z : ℝ →ᵃ[ℝ] H)) := by
    have := h0.comp_affineMap ((AffineMap.lineMap y z : ℝ →ᵃ[ℝ] H))
    rwa [preimage_univ] at this
  have hl : HasDerivAt ((AffineMap.lineMap y z : ℝ →ᵃ[ℝ] H) : ℝ → H) (z - y) 0 := AffineMap.hasDerivAt_lineMap
  have hl0 : (AffineMap.lineMap y z : ℝ →ᵃ[ℝ] H) (0 : ℝ) = y := AffineMap.lineMap_apply_zero y z
  have hf' : HasDerivAt (fun l => f ((AffineMap.lineMap y z : ℝ →ᵃ[ℝ] H) l)) (inner ℝ (gradient f y) (z - y)) 0 := by
    rw [inner_gradient_left]
    have := (hfd ((AffineMap.lineMap y z : ℝ →ᵃ[ℝ] H) (0 : ℝ))).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hl
    rw [hl0] at this
    exact this
  have hn := hl.norm_sq
  rw [hl0] at hn
  have hder : HasDerivAt ((fun x => f x - μ / 2 * ‖x‖ ^ 2) ∘ (AffineMap.lineMap y z : ℝ →ᵃ[ℝ] H))
      (inner ℝ (gradient f y) (z - y) - μ / 2 * (2 * inner ℝ y (z - y))) 0 :=
    hf'.sub (hn.const_mul (μ / 2))
  have hsl := hconv.le_slope_of_hasDerivAt (mem_univ 0) (mem_univ 1) zero_lt_one hder
  rw [slope_def_field] at hsl
  simp only [Function.comp_apply, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one,
    sub_zero, div_one] at hsl
  have e1 : ‖z - y‖ ^ 2 = ‖z‖ ^ 2 - 2 * inner ℝ z y + ‖y‖ ^ 2 := norm_sub_sq_real z y
  have e2 : inner ℝ y (z - y) = inner ℝ z y - ‖y‖ ^ 2 := by
    rw [inner_sub_right, real_inner_self_eq_norm_sq, real_inner_comm]
  rw [e2] at hsl
  rw [e1]
  linarith

/-- The pointwise algebra behind `Ė + (√μ/2) E ≤ -(√μ/8)‖ẋ‖²`. -/
theorem key_vec {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (a w g d : H) (q β P : ℝ) (hq : 0 < q) (hβ0 : 0 ≤ β) (hqβ : q * β ≤ 1 / 2) (hP : 0 ≤ P)
    (hag : P + q ^ 2 / 2 * ‖a‖ ^ 2 ≤ inner ℝ a g) (hd : d = -(q • w) - g) :
    q / 2 * (P + 1 / 2 * ‖q • a + w + β • g‖ ^ 2)
      + (inner ℝ g w + 1 / 2 * (2 * inner ℝ (q • a + w + β • g) d))
      ≤ -(q / 8) * ‖w‖ ^ 2 := by
  subst hd
  have e1 : ‖q • a + w + β • g‖ ^ 2 = q ^ 2 * ‖a‖ ^ 2 + ‖w‖ ^ 2 + β ^ 2 * ‖g‖ ^ 2
      + 2 * q * inner ℝ a w + 2 * q * β * inner ℝ a g + 2 * β * inner ℝ w g := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      real_inner_self_eq_norm_sq, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, real_inner_comm a w, real_inner_comm a g, real_inner_comm w g]
    ring
  have e2 : inner ℝ (q • a + w + β • g) (-(q • w) - g) = -q ^ 2 * inner ℝ a w - q * inner ℝ a g
      - q * ‖w‖ ^ 2 - inner ℝ w g - q * β * inner ℝ w g - β * ‖g‖ ^ 2 := by
    simp only [inner_add_left, inner_sub_right, inner_neg_right, real_inner_smul_left,
      real_inner_smul_right, real_inner_self_eq_norm_sq, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, real_inner_comm a w, real_inner_comm a g,
      real_inner_comm w g]
    ring
  have e3 : ‖(q / 2) • a + w‖ ^ 2 = q ^ 2 / 4 * ‖a‖ ^ 2 + q * inner ℝ a w + ‖w‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      real_inner_self_eq_norm_sq, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, real_inner_comm a w]
    ring
  have e4 : ‖q • w + g‖ ^ 2 = q ^ 2 * ‖w‖ ^ 2 + 2 * q * inner ℝ w g + ‖g‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      real_inner_self_eq_norm_sq, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, real_inner_comm w g]
    ring
  have h1 : 0 ≤ q ^ 2 / 4 * ‖a‖ ^ 2 + q * inner ℝ a w + ‖w‖ ^ 2 := by
    rw [← e3]; positivity
  have h2 : 0 ≤ q ^ 2 * ‖w‖ ^ 2 + 2 * q * inner ℝ w g + ‖g‖ ^ 2 := by
    rw [← e4]; positivity
  rw [e1, e2, real_inner_comm w g]
  have hA : 0 ≤ ‖a‖ ^ 2 := by positivity
  have hW : 0 ≤ ‖w‖ ^ 2 := by positivity
  have hG : 0 ≤ ‖g‖ ^ 2 := by positivity
  have k1 : 0 ≤ q * (1 - q * β / 2) * (inner ℝ a g - P - q ^ 2 / 2 * ‖a‖ ^ 2) :=
    mul_nonneg (mul_nonneg hq.le (by linarith)) (by linarith)
  have k2 : 0 ≤ q * (1 - q * β) * P := mul_nonneg (mul_nonneg hq.le (by linarith)) hP
  have k3 : 0 ≤ q ^ 3 * (1 - 2 * q * β) * ‖a‖ ^ 2 :=
    mul_nonneg (mul_nonneg (by positivity) (by linarith)) hA
  have k4 : 0 ≤ q * (q ^ 2 / 4 * ‖a‖ ^ 2 + q * inner ℝ a w + ‖w‖ ^ 2) := mul_nonneg hq.le h1
  have k5 : 0 ≤ β * (q ^ 2 * ‖w‖ ^ 2 + 2 * q * inner ℝ w g + ‖g‖ ^ 2) := mul_nonneg hβ0 h2
  have k6 : 0 ≤ q * (1 - 2 * q * β) * ‖w‖ ^ 2 := mul_nonneg (mul_nonneg hq.le (by linarith)) hW
  have k7 : 0 ≤ β * (3 - q * β) * ‖g‖ ^ 2 := mul_nonneg (mul_nonneg hβ0 (by linarith)) hG
  nlinarith [k1, k2, k3, k4, k5, k6, k7]

/-- Explicit derivative of the Lyapunov function along the trajectory. -/
noncomputable def Ed {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → ℝ) (μ β : ℝ) (xstar : H) (x xd xdd : ℝ → H) (t : ℝ) : ℝ :=
  inner ℝ (gradient f (x t)) (xd t)
    + 1 / 2 * (2 * inner ℝ (Real.sqrt μ • (x t - xstar) + xd t + β • gradient f (x t))
      (Real.sqrt μ • xd t + xdd t + β • fderiv ℝ (gradient f) (x t) (xd t)))

open HessianDamping.DINSC in
theorem lyap_deriv_bound {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (f : H → ℝ) (hfC2 : ContDiff ℝ 2 f)
    (μ : ℝ) (hμ : 0 < μ) (hsc : IsStronglyConvex f μ)
    (xstar : H) (hxstar : ∀ y, f xstar ≤ f y)
    (t₀ : ℝ) (β : ℝ) (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / (2 * Real.sqrt μ))
    (x xd xdd : ℝ → H) (hx : IsSolution19 f μ β t₀ x xd xdd) (t : ℝ) (ht : t₀ < t) :
    HasDerivAt (lyap f μ β xstar x xd) (Ed f μ β xstar x xd xdd t) t ∧
      Real.sqrt μ / 2 * lyap f μ β xstar x xd t + Ed f μ β xstar x xd xdd t
        ≤ -(Real.sqrt μ / 8) * ‖xd t‖ ^ 2 := by
  have hq0 : 0 < Real.sqrt μ := Real.sqrt_pos.2 hμ
  have hqq : Real.sqrt μ ^ 2 = μ := Real.sq_sqrt hμ.le
  have hqβ : Real.sqrt μ * β ≤ 1 / 2 := by
    have := (le_div_iff₀ (by positivity : (0:ℝ) < 2 * Real.sqrt μ)).1 hβ
    nlinarith
  obtain ⟨h1, h2, h3⟩ := hx t ht.le
  have hn : Ici t₀ ∈ 𝓝 t := Ici_mem_nhds ht
  have hxt := h1.hasDerivAt hn
  have hxdt := h2.hasDerivAt hn
  have hfd : Differentiable ℝ f := hfC2.differentiable (by norm_num)
  have hgd : Differentiable ℝ (gradient f) :=
    (contDiff_one_gradient f hfC2).differentiable (by norm_num)
  have hgt : HasDerivAt (fun τ => gradient f (x τ)) (fderiv ℝ (gradient f) (x t) (xd t)) t :=
    (hgd (x t)).hasFDerivAt.comp_hasDerivAt t hxt
  have hft : HasDerivAt (fun τ => f (x τ)) (inner ℝ (gradient f (x t)) (xd t)) t := by
    rw [inner_gradient_left]; exact (hfd (x t)).hasFDerivAt.comp_hasDerivAt t hxt
  have hv : HasDerivAt (fun τ => Real.sqrt μ • (x τ - xstar) + xd τ + β • gradient f (x τ))
      (Real.sqrt μ • xd t + xdd t + β • fderiv ℝ (gradient f) (x t) (xd t)) t :=
    (((hxt.sub_const xstar).const_smul (Real.sqrt μ)).add hxdt).add (hgt.const_smul β)
  have hE := (hft.sub_const (f xstar)).add (hv.norm_sq.const_mul (1 / 2))
  refine ⟨hE, ?_⟩
  have hv' : Real.sqrt μ • xd t + xdd t + β • fderiv ℝ (gradient f) (x t) (xd t)
      = -(Real.sqrt μ • xd t) - gradient f (x t) := by
    calc _ = (xdd t + (2 * Real.sqrt μ) • xd t + β • fderiv ℝ (gradient f) (x t) (xd t)
            + gradient f (x t)) + (-(Real.sqrt μ • xd t) - gradient f (x t)) := by
          rw [two_mul, add_smul]; abel
      _ = _ := by rw [h3, zero_add]
  have hsc1 := sc_first_order f hfd μ hsc (x t) xstar
  have hP : 0 ≤ f (x t) - f xstar := sub_nonneg.2 (hxstar _)
  have hag : f (x t) - f xstar + Real.sqrt μ ^ 2 / 2 * ‖x t - xstar‖ ^ 2
      ≤ inner ℝ (x t - xstar) (gradient f (x t)) := by
    have e1 : inner ℝ (gradient f (x t)) (xstar - x t) = -inner ℝ (x t - xstar) (gradient f (x t)) := by
      rw [← neg_sub, inner_neg_right, real_inner_comm]
    rw [e1, norm_sub_rev] at hsc1
    rw [hqq]
    linarith
  exact key_vec (x t - xstar) (xd t) (gradient f (x t)) _ (Real.sqrt μ) β (f (x t) - f xstar)
    hq0 hβ0 hqβ hP hag hv'

open HessianDamping.DINSC in
theorem energy_bound {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (f : H → ℝ) (hfC2 : ContDiff ℝ 2 f)
    (μ : ℝ) (hμ : 0 < μ) (hsc : IsStronglyConvex f μ)
    (xstar : H) (hxstar : ∀ y, f xstar ≤ f y)
    (t₀ : ℝ) (β : ℝ) (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / (2 * Real.sqrt μ))
    (x xd xdd : ℝ → H) (hx : IsSolution19 f μ β t₀ x xd xdd) :
    ∀ t ∈ Ici t₀, (∫ τ in t₀..t, Real.exp (Real.sqrt μ / 2 * τ) * ‖xd τ‖ ^ 2)
      ≤ 8 / Real.sqrt μ * (Real.exp (Real.sqrt μ / 2 * t₀) * lyap f μ β xstar x xd t₀)
        - 8 / Real.sqrt μ * (Real.exp (Real.sqrt μ / 2 * t) * lyap f μ β xstar x xd t) := by
  intro t ht
  have hq0 : 0 < Real.sqrt μ := Real.sqrt_pos.2 hμ
  have hfd : Differentiable ℝ f := hfC2.differentiable (by norm_num)
  have hgc : Continuous (gradient f) := (contDiff_one_gradient f hfC2).continuous
  have hxc : ContinuousOn x (Ici t₀) := fun τ hτ => (hx τ hτ).1.continuousWithinAt
  have hxdc : ContinuousOn xd (Ici t₀) := fun τ hτ => (hx τ hτ).2.1.continuousWithinAt
  have hfx : ContinuousOn (fun τ => f (x τ)) (Ici t₀) := hfd.continuous.comp_continuousOn hxc
  have hgx : ContinuousOn (fun τ => gradient f (x τ)) (Ici t₀) := hgc.comp_continuousOn hxc
  have hEc : ContinuousOn (lyap f μ β xstar x xd) (Ici t₀) := by
    unfold lyap
    exact (hfx.sub continuousOn_const).add (continuousOn_const.mul
      ((((continuousOn_const.smul (hxc.sub continuousOn_const)).add hxdc).add
        (continuousOn_const.smul hgx)).norm.pow 2))
  have hexpc : Continuous (fun τ : ℝ => Real.exp (Real.sqrt μ / 2 * τ)) :=
    Real.continuous_exp.comp (continuous_const.mul continuous_id)
  have hexp : ∀ τ : ℝ, HasDerivAt (fun τ => Real.exp (Real.sqrt μ / 2 * τ))
      (Real.exp (Real.sqrt μ / 2 * τ) * (Real.sqrt μ / 2)) τ := fun τ => by
    simpa using ((hasDerivAt_id τ).const_mul (Real.sqrt μ / 2)).exp
  have hcont : ContinuousOn (fun τ => -(8 / Real.sqrt μ) *
      (Real.exp (Real.sqrt μ / 2 * τ) * lyap f μ β xstar x xd τ)) (Icc t₀ t) :=
    continuousOn_const.mul (hexpc.continuousOn.mul (hEc.mono Icc_subset_Ici_self))
  have hderiv : ∀ τ ∈ Ioo t₀ t, HasDerivWithinAt (fun τ => -(8 / Real.sqrt μ) *
      (Real.exp (Real.sqrt μ / 2 * τ) * lyap f μ β xstar x xd τ))
      (-(8 / Real.sqrt μ) * (Real.exp (Real.sqrt μ / 2 * τ) * (Real.sqrt μ / 2)
        * lyap f μ β xstar x xd τ
        + Real.exp (Real.sqrt μ / 2 * τ) * Ed f μ β xstar x xd xdd τ)) (Ioi τ) τ := by
    intro τ hτ
    have hd := (lyap_deriv_bound f hfC2 μ hμ hsc xstar hxstar t₀ β hβ0 hβ x xd xdd hx τ hτ.1).1
    exact (((hexp τ).mul hd).const_mul _).hasDerivWithinAt
  have hφint : IntegrableOn (fun τ => Real.exp (Real.sqrt μ / 2 * τ) * ‖xd τ‖ ^ 2) (Icc t₀ t) :=
    ContinuousOn.integrableOn_Icc
      (hexpc.continuousOn.mul ((hxdc.mono Icc_subset_Ici_self).norm.pow 2))
  have hφg : ∀ τ ∈ Ioo t₀ t, Real.exp (Real.sqrt μ / 2 * τ) * ‖xd τ‖ ^ 2 ≤
      -(8 / Real.sqrt μ) * (Real.exp (Real.sqrt μ / 2 * τ) * (Real.sqrt μ / 2)
        * lyap f μ β xstar x xd τ
        + Real.exp (Real.sqrt μ / 2 * τ) * Ed f μ β xstar x xd xdd τ) := by
    intro τ hτ
    have hb := (lyap_deriv_bound f hfC2 μ hμ hsc xstar hxstar t₀ β hβ0 hβ x xd xdd hx τ hτ.1).2
    have he := Real.exp_pos (Real.sqrt μ / 2 * τ)
    have h1 := mul_le_mul_of_nonneg_left hb he.le
    have h8 : 0 < 8 / Real.sqrt μ := div_pos (by norm_num) hq0
    have h2 := mul_le_mul_of_nonpos_left h1 (by linarith : -(8 / Real.sqrt μ) ≤ 0)
    have hq8 : 8 / Real.sqrt μ * (Real.sqrt μ / 8) = 1 := by
      rw [show 8 / Real.sqrt μ * (Real.sqrt μ / 8) = Real.sqrt μ / Real.sqrt μ by ring,
        div_self hq0.ne']
    have e3 : -(8 / Real.sqrt μ) * (Real.exp (Real.sqrt μ / 2 * τ) *
        (-(Real.sqrt μ / 8) * ‖xd τ‖ ^ 2)) = Real.exp (Real.sqrt μ / 2 * τ) * ‖xd τ‖ ^ 2 := by
      calc _ = 8 / Real.sqrt μ * (Real.sqrt μ / 8) * (Real.exp (Real.sqrt μ / 2 * τ) * ‖xd τ‖ ^ 2) := by
            ring
        _ = _ := by rw [hq8, one_mul]
    rw [e3] at h2
    have e4 : -(8 / Real.sqrt μ) * (Real.exp (Real.sqrt μ / 2 * τ) * (Real.sqrt μ / 2)
        * lyap f μ β xstar x xd τ + Real.exp (Real.sqrt μ / 2 * τ) * Ed f μ β xstar x xd xdd τ)
        = -(8 / Real.sqrt μ) * (Real.exp (Real.sqrt μ / 2 * τ) * (Real.sqrt μ / 2
          * lyap f μ β xstar x xd τ + Ed f μ β xstar x xd xdd τ)) := by ring
    rw [e4]
    exact h2
  have hint := intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le ht hcont hderiv hφint hφg
  linarith

end HD7Aux

open HessianDamping.DINSC Set Filter Topology MeasureTheory in
theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → ℝ) (hfconv : ConvexOn ℝ Set.univ f) (hfC2 : ContDiff ℝ 2 f)
    (μ : ℝ) (hμ : 0 < μ) (hsc : IsStronglyConvex f μ)
    (xstar : H) (hxstar : ∀ y, f xstar ≤ f y)
    (t₀ : ℝ) (ht₀ : 0 < t₀)
    (β : ℝ) (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / (2 * Real.sqrt μ))
    (x xd xdd : ℝ → H) (hx : IsSolution19 f μ β t₀ x xd xdd) :
    (∀ t ∈ Ici t₀, μ / 2 * ‖x t - xstar‖ ^ 2 ≤ f (x t) - f xstar ∧
      f (x t) - f xstar ≤
        (f (x t₀) - f xstar + μ * ‖x t₀ - xstar‖ ^ 2 + ‖xd t₀ + β • gradient f (x t₀)‖ ^ 2)
          * Real.exp (-(Real.sqrt μ / 2) * (t - t₀))) ∧
    (∃ C₁ : ℝ, 0 < C₁ ∧ ∀ t ∈ Ici t₀,
      Real.exp (-(Real.sqrt μ) * t) *
          ∫ s in t₀..t, Real.exp (Real.sqrt μ * s) * ‖gradient f (x s)‖ ^ 2
        ≤ C₁ * Real.exp (-(Real.sqrt μ / 2) * t)) ∧
    MeasureTheory.IntegrableOn (fun t => Real.exp (Real.sqrt μ / 2 * t) * ‖xd t‖ ^ 2) (Ici t₀) := by
  have hq0 : 0 < Real.sqrt μ := Real.sqrt_pos.2 hμ
  have hqq : Real.sqrt μ ^ 2 = μ := Real.sq_sqrt hμ.le
  have hfd : Differentiable ℝ f := hfC2.differentiable (by norm_num)
  have hg1 := HD7Aux.contDiff_one_gradient f hfC2
  have hgc : Continuous (gradient f) := hg1.continuous
  have hxc : ContinuousOn x (Ici t₀) := fun τ hτ => (hx τ hτ).1.continuousWithinAt
  have hxdc : ContinuousOn xd (Ici t₀) := fun τ hτ => (hx τ hτ).2.1.continuousWithinAt
  have hgx : ContinuousOn (fun τ => gradient f (x τ)) (Ici t₀) := hgc.comp_continuousOn hxc
  have hexpc : ∀ c : ℝ, Continuous (fun τ : ℝ => Real.exp (c * τ)) := fun c =>
    Real.continuous_exp.comp (continuous_const.mul continuous_id)
  have hexp : ∀ τ : ℝ, HasDerivAt (fun τ => Real.exp (Real.sqrt μ / 2 * τ))
      (Real.exp (Real.sqrt μ / 2 * τ) * (Real.sqrt μ / 2)) τ := fun τ => by
    simpa using ((hasDerivAt_id τ).const_mul (Real.sqrt μ / 2)).exp
  have hEb := HD7Aux.energy_bound f hfC2 μ hμ hsc xstar hxstar t₀ β hβ0 hβ x xd xdd hx
  have hP : ∀ τ, 0 ≤ f (x τ) - f xstar := fun τ => sub_nonneg.2 (hxstar _)
  have hE0 : ∀ τ, 0 ≤ lyap f μ β xstar x xd τ := fun τ => by
    unfold lyap; exact add_nonneg (hP τ) (by positivity)
  have hint0 : ∀ t ∈ Ici t₀, 0 ≤ ∫ τ in t₀..t, Real.exp (Real.sqrt μ / 2 * τ) * ‖xd τ‖ ^ 2 :=
    fun t ht => intervalIntegral.integral_nonneg ht (fun τ _ => by positivity)
  have hFdec : ∀ t ∈ Ici t₀, Real.exp (Real.sqrt μ / 2 * t) * lyap f μ β xstar x xd t
      ≤ Real.exp (Real.sqrt μ / 2 * t₀) * lyap f μ β xstar x xd t₀ := by
    intro t ht
    have h1 := hEb t ht
    have h2 := hint0 t ht
    have h3 : 0 ≤ 8 / Real.sqrt μ * (Real.exp (Real.sqrt μ / 2 * t₀) * lyap f μ β xstar x xd t₀
        - Real.exp (Real.sqrt μ / 2 * t) * lyap f μ β xstar x xd t) := by
      rw [mul_sub]; linarith
    have h4 := (mul_nonneg_iff_of_pos_left (div_pos (by norm_num : (0:ℝ) < 8) hq0)).1 h3
    linarith
  have hgrad0 : gradient f xstar = 0 := by
    have hmin : IsLocalMin f xstar := Filter.Eventually.of_forall hxstar
    simp [gradient, hmin.fderiv_eq_zero]
  have hi : ∀ t ∈ Ici t₀, μ / 2 * ‖x t - xstar‖ ^ 2 ≤ f (x t) - f xstar ∧
      f (x t) - f xstar ≤
        (f (x t₀) - f xstar + μ * ‖x t₀ - xstar‖ ^ 2 + ‖xd t₀ + β • gradient f (x t₀)‖ ^ 2)
          * Real.exp (-(Real.sqrt μ / 2) * (t - t₀)) := by
    intro t ht
    constructor
    · have h := HD7Aux.sc_first_order f hfd μ hsc xstar (x t)
      rw [hgrad0, inner_zero_left] at h
      linarith
    · have hEt : f (x t) - f xstar ≤ lyap f μ β xstar x xd t := by
        unfold lyap
        have : 0 ≤ 1 / 2 * ‖Real.sqrt μ • (x t - xstar) + xd t + β • gradient f (x t)‖ ^ 2 := by
          positivity
        linarith
      have hE0C : lyap f μ β xstar x xd t₀ ≤ f (x t₀) - f xstar + μ * ‖x t₀ - xstar‖ ^ 2
          + ‖xd t₀ + β • gradient f (x t₀)‖ ^ 2 := by
        unfold lyap
        have hpr : Real.sqrt μ • (x t₀ - xstar) + xd t₀ + β • gradient f (x t₀)
            = Real.sqrt μ • (x t₀ - xstar) + (xd t₀ + β • gradient f (x t₀)) := add_assoc _ _ _
        rw [hpr]
        have hp : ‖Real.sqrt μ • (x t₀ - xstar)‖ ^ 2 = μ * ‖x t₀ - xstar‖ ^ 2 := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hq0, mul_pow, hqq]
        have hn := norm_add_le (Real.sqrt μ • (x t₀ - xstar)) (xd t₀ + β • gradient f (x t₀))
        have hm := mul_nonneg (sub_nonneg.2 hn) (add_nonneg (add_nonneg
          (norm_nonneg (Real.sqrt μ • (x t₀ - xstar))) (norm_nonneg (xd t₀ + β • gradient f (x t₀))))
          (norm_nonneg (Real.sqrt μ • (x t₀ - xstar) + (xd t₀ + β • gradient f (x t₀)))))
        nlinarith [sq_nonneg (‖Real.sqrt μ • (x t₀ - xstar)‖ - ‖xd t₀ + β • gradient f (x t₀)‖)]
      have hdec : lyap f μ β xstar x xd t ≤
          lyap f μ β xstar x xd t₀ * Real.exp (-(Real.sqrt μ / 2) * (t - t₀)) := by
        have h := hFdec t ht
        have he : Real.exp (Real.sqrt μ / 2 * t₀) = Real.exp (Real.sqrt μ / 2 * t)
            * Real.exp (-(Real.sqrt μ / 2) * (t - t₀)) := by
          rw [← Real.exp_add]; congr 1; ring
        rw [he] at h
        have hpos := Real.exp_pos (Real.sqrt μ / 2 * t)
        have h' : Real.exp (Real.sqrt μ / 2 * t) * lyap f μ β xstar x xd t ≤
            Real.exp (Real.sqrt μ / 2 * t) * (lyap f μ β xstar x xd t₀
              * Real.exp (-(Real.sqrt μ / 2) * (t - t₀))) := by linarith
        exact le_of_mul_le_mul_left h' hpos
      calc f (x t) - f xstar ≤ lyap f μ β xstar x xd t := hEt
        _ ≤ lyap f μ β xstar x xd t₀ * Real.exp (-(Real.sqrt μ / 2) * (t - t₀)) := hdec
        _ ≤ _ := mul_le_mul_of_nonneg_right hE0C (Real.exp_pos _).le
  refine ⟨hi, ?_, ?_⟩
  · obtain ⟨K, U, hU, hLip⟩ := (hg1.contDiffAt (x := xstar)).exists_lipschitzOnWith
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 hU
    obtain ⟨C, hCnn, hCdef⟩ : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ici t₀,
        ‖x t - xstar‖ ^ 2 ≤ C * Real.exp (-(Real.sqrt μ / 2) * (t - t₀)) := by
      refine ⟨(f (x t₀) - f xstar + μ * ‖x t₀ - xstar‖ ^ 2
        + ‖xd t₀ + β • gradient f (x t₀)‖ ^ 2) / (μ / 2), ?_, ?_⟩
      · exact div_nonneg (add_nonneg (add_nonneg (hP t₀) (by positivity)) (by positivity))
          (by positivity)
      · intro t ht
        have h := hi t ht
        rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
        linarith [h.1.trans h.2]
    have htend : Tendsto (fun τ => C * Real.exp (-(Real.sqrt μ / 2) * (τ - t₀))) atTop (𝓝 0) := by
      have h0 : Tendsto (fun τ : ℝ => τ - t₀) atTop atTop :=
        Filter.tendsto_atTop_atTop.2 fun b => ⟨b + t₀, fun a ha => by linarith⟩
      have h1 : Tendsto (fun τ : ℝ => -(Real.sqrt μ / 2) * (τ - t₀)) atTop atBot :=
        h0.const_mul_atTop_of_neg (by linarith)
      simpa using (Real.tendsto_exp_atBot.comp h1).const_mul C
    obtain ⟨T, hT⟩ := eventually_atTop.1
      (htend.eventually (gt_mem_nhds (by positivity : (0:ℝ) < r ^ 2)))
    obtain ⟨M, hM⟩ := (isCompact_Icc (a := t₀) (b := max T t₀)).exists_bound_of_continuousOn
      (hgx.mono Icc_subset_Ici_self)
    have hstar : xstar ∈ U := hball (Metric.mem_ball_self hr)
    obtain ⟨K', hK'pos, hgb⟩ : ∃ K' : ℝ, 0 < K' ∧ ∀ τ ∈ Ici t₀,
        ‖gradient f (x τ)‖ ^ 2 ≤ K' * Real.exp (-(Real.sqrt μ / 2) * τ) := by
      have a1 : 0 ≤ M ^ 2 * Real.exp (Real.sqrt μ / 2 * max T t₀) := by positivity
      have a2 : 0 ≤ (K : ℝ) ^ 2 * C * Real.exp (Real.sqrt μ / 2 * t₀) :=
        mul_nonneg (mul_nonneg (by positivity) hCnn) (by positivity)
      refine ⟨M ^ 2 * Real.exp (Real.sqrt μ / 2 * max T t₀)
        + (K : ℝ) ^ 2 * C * Real.exp (Real.sqrt μ / 2 * t₀) + 1, by linarith, fun τ hτ => ?_⟩
      have he := Real.exp_pos (-(Real.sqrt μ / 2) * τ)
      by_cases hτT : τ ≤ max T t₀
      · have h1 : ‖gradient f (x τ)‖ ^ 2 ≤ M ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (hM τ ⟨hτ, hτT⟩) 2
        have h2 : 1 ≤ Real.exp (Real.sqrt μ / 2 * max T t₀) * Real.exp (-(Real.sqrt μ / 2) * τ) := by
          rw [← Real.exp_add]; exact Real.one_le_exp (by nlinarith)
        nlinarith [mul_nonneg a2 he.le, mul_le_mul_of_nonneg_left h2 (sq_nonneg M)]
      · rw [not_le] at hτT
        have hτT0 : T ≤ τ := le_trans (le_max_left _ _) hτT.le
        have hA := hCdef τ hτ
        have hlt : ‖x τ - xstar‖ < r := lt_of_pow_lt_pow_left₀ 2 hr.le (hA.trans_lt (hT τ hτT0))
        have hmem : x τ ∈ U := hball (by rw [Metric.mem_ball, dist_eq_norm]; exact hlt)
        have hL := hLip.dist_le_mul (x τ) hmem xstar hstar
        rw [dist_eq_norm, dist_eq_norm, hgrad0, sub_zero] at hL
        have h1 : ‖gradient f (x τ)‖ ^ 2 ≤ (K : ℝ) ^ 2 * ‖x τ - xstar‖ ^ 2 := by
          calc _ ≤ ((K : ℝ) * ‖x τ - xstar‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hL 2
            _ = _ := by ring
        have he2 : Real.exp (-(Real.sqrt μ / 2) * (τ - t₀)) =
            Real.exp (Real.sqrt μ / 2 * t₀) * Real.exp (-(Real.sqrt μ / 2) * τ) := by
          rw [← Real.exp_add]; congr 1; ring
        rw [he2] at hA
        have h3 := mul_le_mul_of_nonneg_left hA (by positivity : (0:ℝ) ≤ (K : ℝ) ^ 2)
        nlinarith [mul_nonneg a1 he.le]
    refine ⟨2 * K' / Real.sqrt μ, div_pos (by linarith) hq0, fun t ht => ?_⟩
    have hderiv : ∀ τ ∈ Ioo t₀ t, HasDerivWithinAt
        (fun τ => 2 * K' / Real.sqrt μ * Real.exp (Real.sqrt μ / 2 * τ))
        (K' * Real.exp (Real.sqrt μ / 2 * τ)) (Ioi τ) τ := by
      intro τ _
      have h := (hexp τ).const_mul (2 * K' / Real.sqrt μ)
      refine (h.congr_deriv ?_).hasDerivWithinAt
      rw [show 2 * K' / Real.sqrt μ * (Real.exp (Real.sqrt μ / 2 * τ) * (Real.sqrt μ / 2))
          = K' * Real.exp (Real.sqrt μ / 2 * τ) * (Real.sqrt μ / Real.sqrt μ) by ring,
        div_self hq0.ne', mul_one]
    have hgcont : ContinuousOn (fun τ => 2 * K' / Real.sqrt μ * Real.exp (Real.sqrt μ / 2 * τ))
        (Icc t₀ t) := (continuous_const.mul (hexpc _)).continuousOn
    have hφc : ContinuousOn (fun τ => Real.exp (Real.sqrt μ * τ) * ‖gradient f (x τ)‖ ^ 2)
        (Icc t₀ t) := (hexpc _).continuousOn.mul ((hgx.mono Icc_subset_Ici_self).norm.pow 2)
    have hφg : ∀ τ ∈ Ioo t₀ t, Real.exp (Real.sqrt μ * τ) * ‖gradient f (x τ)‖ ^ 2
        ≤ K' * Real.exp (Real.sqrt μ / 2 * τ) := by
      intro τ hτ
      have h := mul_le_mul_of_nonneg_left (hgb τ (le_of_lt hτ.1)) (Real.exp_pos (Real.sqrt μ * τ)).le
      have e : Real.exp (Real.sqrt μ * τ) * (K' * Real.exp (-(Real.sqrt μ / 2) * τ))
          = K' * Real.exp (Real.sqrt μ / 2 * τ) := by
        rw [mul_left_comm, ← Real.exp_add]; congr 2; ring
      linarith
    have hint := intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le ht hgcont hderiv
      hφc.integrableOn_Icc hφg
    have hint' : (∫ s in t₀..t, Real.exp (Real.sqrt μ * s) * ‖gradient f (x s)‖ ^ 2)
        ≤ 2 * K' / Real.sqrt μ * Real.exp (Real.sqrt μ / 2 * t) := by
      have : 0 ≤ 2 * K' / Real.sqrt μ * Real.exp (Real.sqrt μ / 2 * t₀) :=
        mul_nonneg (div_nonneg (by linarith) hq0.le) (Real.exp_pos _).le
      linarith
    calc _ ≤ Real.exp (-(Real.sqrt μ) * t) * (2 * K' / Real.sqrt μ * Real.exp (Real.sqrt μ / 2 * t)) :=
          mul_le_mul_of_nonneg_left hint' (Real.exp_pos _).le
      _ = 2 * K' / Real.sqrt μ * Real.exp (-(Real.sqrt μ / 2) * t) := by
          rw [mul_left_comm, ← Real.exp_add]; congr 2; ring
  · have hφc : ContinuousOn (fun t => Real.exp (Real.sqrt μ / 2 * t) * ‖xd t‖ ^ 2) (Ici t₀) :=
      (hexpc _).continuousOn.mul (hxdc.norm.pow 2)
    have hIoi : IntegrableOn (fun t => Real.exp (Real.sqrt μ / 2 * t) * ‖xd t‖ ^ 2) (Ioi t₀) := by
      refine integrableOn_Ioi_of_intervalIntegral_norm_bounded
        (8 / Real.sqrt μ * (Real.exp (Real.sqrt μ / 2 * t₀) * lyap f μ β xstar x xd t₀)) t₀
        (fun i => ((hφc.mono Icc_subset_Ici_self).integrableOn_Icc).mono_set Ioc_subset_Icc_self)
        tendsto_id ?_
      filter_upwards [eventually_ge_atTop t₀] with i hi
      simp only [id, norm_mul, norm_pow, Real.norm_eq_abs, Real.abs_exp, abs_norm]
      have h1 := hEb i hi
      have h2 : 0 ≤ 8 / Real.sqrt μ * (Real.exp (Real.sqrt μ / 2 * i) * lyap f μ β xstar x xd i) :=
        mul_nonneg (by positivity) (mul_nonneg (Real.exp_pos _).le (hE0 i))
      linarith
    have hIcc : IntegrableOn (fun t => Real.exp (Real.sqrt μ / 2 * t) * ‖xd t‖ ^ 2) (Icc t₀ t₀) :=
      (hφc.mono Icc_subset_Ici_self).integrableOn_Icc
    refine (hIcc.union hIoi).mono_set ?_
    intro y hy
    rcases eq_or_lt_of_le (show t₀ ≤ y from hy) with h | h
    · exact Or.inl ⟨le_of_eq h, le_of_eq h.symm⟩
    · exact Or.inr h
