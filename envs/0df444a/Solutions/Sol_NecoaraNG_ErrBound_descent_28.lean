-- Prove2me | solution 1 for NecoaraNG.ErrBound.descent_28
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T23:08:23.732895+00:00
-- url     : https://prove2.me/submissions/8f0c7464-b62a-4929-b3ff-b8f6fefdeb39

import Mathlib
import Definitions.Def_NecoaraNG_ErrBound_Setting

set_option autoImplicit false
open scoped InnerProductSpace

section NGSec
open scoped InnerProductSpace
open NecoaraNG.Chain Filter Topology

namespace NGCore
variable {n : ℕ}

theorem inner_grad_eq (f : E n → ℝ) (p v : E n) : ⟪gradient f p, v⟫_ℝ = fderiv ℝ f p v := by
  unfold gradient
  rw [InnerProductSpace.toDual_symm_apply]

theorem line_mem {X : Set (E n)} (hX : Convex ℝ X) {x y : E n} (hx : x ∈ X) (hy : y ∈ X)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) : x + t • (y - x) ∈ X := by
  have := hX hx hy (a := 1 - t) (b := t) (by linarith [ht.2]) ht.1 (by ring)
  convert this using 1
  module

theorem line_hasDeriv {f : E n → ℝ} {p : E n} (hp : DifferentiableAt ℝ f p) (x v : E n) (t : ℝ)
    (hpt : x + t • v = p) :
    HasDerivAt (fun s : ℝ => f (x + s • v)) (⟪gradient f p, v⟫_ℝ) t := by
  have h1 : HasDerivAt (fun s : ℝ => x + s • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  rw [inner_grad_eq]
  subst hpt
  exact hp.hasFDerivAt.comp_hasDerivAt t h1

theorem descent {X : Set (E n)} (hX : Convex ℝ X) {f : E n → ℝ}
    (hd : ∀ x ∈ X, DifferentiableAt ℝ f x) {L : ℝ}
    (hL : ∀ x ∈ X, ∀ y ∈ X, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    {x y : E n} (hx : x ∈ X) (hy : y ∈ X) :
    f y ≤ f x + ⟪gradient f x, y - x⟫_ℝ + L / 2 * ‖y - x‖ ^ 2 := by
  set v := y - x with hv
  let g : ℝ → ℝ := fun s => f (x + s • v) - s * ⟪gradient f x, v⟫_ℝ - L / 2 * s ^ 2 * ‖v‖ ^ 2
  have hder : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasDerivAt g
      (⟪gradient f (x + s • v), v⟫_ℝ - ⟪gradient f x, v⟫_ℝ - L * s * ‖v‖ ^ 2) s := by
    intro s hs
    have hm := line_mem hX hx hy hs
    have h1 := line_hasDeriv (hd _ hm) x v s rfl
    have h2 : HasDerivAt (fun s : ℝ => s * ⟪gradient f x, v⟫_ℝ) (⟪gradient f x, v⟫_ℝ) s := by
      simpa using (hasDerivAt_id s).mul_const (⟪gradient f x, v⟫_ℝ)
    have h3 : HasDerivAt (fun s : ℝ => L / 2 * s ^ 2 * ‖v‖ ^ 2) (L * s * ‖v‖ ^ 2) s := by
      have := ((hasDerivAt_pow 2 s).const_mul (L / 2)).mul_const (‖v‖ ^ 2)
      refine this.congr_deriv ?_
      first | ring | (norm_num; ring) | norm_num
    exact (h1.sub h2).sub h3
  have hanti : AntitoneOn g (Set.Icc 0 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
    · intro s hs; exact (hder s hs).continuousAt.continuousWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      exact (hder s (Set.Ioo_subset_Icc_self hs)).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      have hs' := Set.Ioo_subset_Icc_self hs
      rw [(hder s hs').deriv]
      have hm := line_mem hX hx hy hs'
      have h1 := hL _ hm x hx
      have hn : ‖x + s • v - x‖ = s * ‖v‖ := by
        simp [norm_smul, abs_of_pos hs.1]
      rw [hn] at h1
      have hcs := real_inner_le_norm (gradient f (x + s • v) - gradient f x) v
      rw [inner_sub_left] at hcs
      have h4 := mul_le_mul_of_nonneg_right h1 (norm_nonneg v)
      nlinarith
  have := hanti (Set.left_mem_Icc.2 zero_le_one) (Set.right_mem_Icc.2 zero_le_one) zero_le_one
  have e : x + (1 : ℝ) • v = y := by simp [hv]
  simp only [g, e, zero_smul, add_zero, zero_mul, sub_zero, one_mul, one_pow, mul_zero, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_one] at this
  linarith

theorem convex_ineq {X : Set (E n)} {f : E n → ℝ} (hf : ConvexOn ℝ X f)
    (hd : ∀ x ∈ X, DifferentiableAt ℝ f x) {x y : E n} (hx : x ∈ X) (hy : y ∈ X) :
    f x + ⟪gradient f x, y - x⟫_ℝ ≤ f y := by
  have h1 := line_hasDeriv (hd x hx) x (y - x) 0 (by simp)
  have h2 := h1.tendsto_slope_zero_right
  have h3 : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      t⁻¹ • ((fun s : ℝ => f (x + s • (y - x))) (0 + t) - (fun s : ℝ => f (x + s • (y - x))) 0)
        ≤ f y - f x := by
    filter_upwards [Ioc_mem_nhdsGT zero_lt_one] with t ht
    have hc := hf.2 hx hy (by linarith [ht.2] : (0 : ℝ) ≤ 1 - t) ht.1.le (by ring : (1 - t) + t = 1)
    have e : (1 - t) • x + t • y = x + t • (y - x) := by module
    rw [e] at hc
    simp only [smul_eq_mul, zero_add, zero_smul, add_zero] at hc ⊢
    rw [inv_mul_le_iff₀ ht.1]
    nlinarith
  have := le_of_tendsto h2 h3
  linarith

theorem proj_ineq {X : Set (E n)} (hX : Convex ℝ X) {u p : E n} (hp : IsNearest X u p)
    {z : E n} (hz : z ∈ X) : ⟪u - p, z - p⟫_ℝ ≤ 0 := by
  by_contra hcon
  push Not at hcon
  set a := ⟪u - p, z - p⟫_ℝ with ha
  set b := ‖z - p‖ ^ 2 with hb
  have key : ∀ t : ℝ, 0 < t → t ≤ 1 → 2 * a ≤ t * b := by
    intro t ht0 ht1
    have hq := line_mem hX hp.1 hz ⟨ht0.le, ht1⟩
    have h1 := hp.2 _ hq
    have h2 : ‖u - p‖ ^ 2 ≤ ‖u - (p + t • (z - p))‖ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    have e : u - (p + t • (z - p)) = (u - p) - t • (z - p) := by module
    rw [e] at h2
    have h3 := norm_sub_sq_real (u - p) (t • (z - p))
    have h4 : ‖t • (z - p)‖ ^ 2 = t ^ 2 * b := by
      rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    rw [real_inner_smul_right] at h3
    have : t * (t * b - 2 * a) ≥ 0 := by nlinarith
    have := (mul_nonneg_iff_of_pos_left ht0).1 this
    linarith
  have hb0 : 0 < b := by
    have := key 1 one_pos le_rfl
    linarith
  have h1 := key (min 1 (a / b)) (lt_min one_pos (div_pos hcon hb0)) (min_le_left _ _)
  have h2 : min 1 (a / b) * b ≤ a / b * b :=
    mul_le_mul_of_nonneg_right (min_le_right _ _) hb0.le
  rw [div_mul_cancel₀ _ hb0.ne'] at h2
  linarith

theorem exists_nearest {S : Set (E n)} (hS : IsClosed S) (hne : S.Nonempty) (u : E n) :
    ∃ p, IsNearest S u p := by
  obtain ⟨p, hp, hd⟩ := hS.exists_infDist_eq_dist hne u
  refine ⟨p, hp, fun z hz => ?_⟩
  have := Metric.infDist_le_dist_of_mem (x := u) hz
  rw [dist_eq_norm] at this hd
  linarith

theorem optSet_closed {X : Set (E n)} (hXc : IsClosed X) {f : E n → ℝ}
    (hd : ∀ x ∈ X, DifferentiableAt ℝ f x) {xstar : E n} (h : xstar ∈ optSet X f) :
    IsClosed (optSet X f) := by
  have hc : ContinuousOn f X := fun x hx => (hd x hx).continuousAt.continuousWithinAt
  have : optSet X f = X ∩ f ⁻¹' Set.Iic (f xstar) := by
    ext x
    simp only [optSet, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iic]
    constructor
    · rintro ⟨hx, hmin⟩; exact ⟨hx, hmin _ h.1⟩
    · rintro ⟨hx, hle⟩; exact ⟨hx, fun y hy => hle.trans (h.2 y hy)⟩
  rw [this]
  exact hc.preimage_isClosed_of_isClosed hXc isClosed_Iic

theorem nearest_norm_eq {S : Set (E n)} {u p q : E n} (hp : IsNearest S u p) (hq : IsNearest S u q) :
    ‖u - p‖ = ‖u - q‖ := le_antisymm (hp.2 q hq.1) (hq.2 p hp.1)

theorem opt_val {X : Set (E n)} {f : E n → ℝ} {xstar xb : E n} (h : xstar ∈ optSet X f)
    (hb : xb ∈ optSet X f) : f xb = f xstar :=
  le_antisymm (hb.2 _ h.1) (h.2 _ hb.1)

/-- descent from projection inequality with comparison point `xk` -/
theorem descent_core {X : Set (E n)} (hX : Convex ℝ X) {f : E n → ℝ}
    (hd : ∀ x ∈ X, DifferentiableAt ℝ f x) {L : ℝ}
    (hL : ∀ x ∈ X, ∀ y ∈ X, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    {α : ℝ} (hα : 0 < α) {xk xk1 : E n} (hxk : xk ∈ X)
    (hn : IsNearest X (xk - α • gradient f xk) xk1) :
    f xk1 ≤ f xk + (L / 2 - 1 / α) * ‖xk1 - xk‖ ^ 2 := by
  have hP := proj_ineq hX hn hxk
  have e : xk - α • gradient f xk - xk1 = (xk - xk1) - α • gradient f xk := by module
  rw [e, inner_sub_left, real_inner_smul_left] at hP
  have e2 : ⟪xk - xk1, xk - xk1⟫_ℝ = ‖xk1 - xk‖ ^ 2 := by
    rw [real_inner_self_eq_norm_sq, norm_sub_rev]
  have e4 : ⟪gradient f xk, xk1 - xk⟫_ℝ = -⟪gradient f xk, xk - xk1⟫_ℝ := by
    rw [← inner_neg_right]; congr 1; abel
  have hd1 := descent hX hd hL hxk hn.1
  rw [e2] at hP
  set I4 := ⟪gradient f xk, xk - xk1⟫_ℝ
  set D := ‖xk1 - xk‖ ^ 2
  have h5 : 1 / α * D ≤ I4 := by
    rw [one_div, inv_mul_le_iff₀ hα]
    linarith
  rw [e4] at hd1
  linarith

/-- main one-step inequality -/
theorem step_ineq {X : Set (E n)} (hX : Convex ℝ X) {f : E n → ℝ}
    (hd : ∀ x ∈ X, DifferentiableAt ℝ f x) {L : ℝ}
    (hL : ∀ x ∈ X, ∀ y ∈ X, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    {α : ℝ} (hα : 0 < α) (hαL : α * L ≤ 1) {xk xk1 xb : E n} (hxk : xk ∈ X)
    (hn : IsNearest X (xk - α • gradient f xk) xk1) (hxb : xb ∈ X) (c : ℝ)
    (hc : ⟪gradient f xk, xb - xk⟫_ℝ ≤ f xb - f xk - c / 2 * ‖xk - xb‖ ^ 2) :
    ‖xk1 - xb‖ ^ 2 ≤ (1 - α * c) * ‖xk - xb‖ ^ 2 - 2 * α * (f xk1 - f xb) := by
  have hP := proj_ineq hX hn hxb
  have e : xk - α • gradient f xk - xk1 = (xk - xk1) - α • gradient f xk := by module
  rw [e, inner_sub_left, real_inner_smul_left] at hP
  have e1 : ‖xk1 - xb‖ ^ 2 = ‖xk - xb‖ ^ 2 - ‖xk - xk1‖ ^ 2 - 2 * ⟪xk - xk1, xk1 - xb⟫_ℝ := by
    have : xk - xb = (xk - xk1) + (xk1 - xb) := by abel
    rw [this, norm_add_sq_real]; ring
  have e2 : ⟪xk - xk1, xb - xk1⟫_ℝ = -⟪xk - xk1, xk1 - xb⟫_ℝ := by
    rw [← inner_neg_right]; congr 1; abel
  have e3 : ⟪gradient f xk, xb - xk1⟫_ℝ =
      ⟪gradient f xk, xb - xk⟫_ℝ + ⟪gradient f xk, xk - xk1⟫_ℝ := by
    rw [← inner_add_right]; congr 1; abel
  have hd1 := descent hX hd hL hxk hn.1
  have e4 : ⟪gradient f xk, xk1 - xk⟫_ℝ = -⟪gradient f xk, xk - xk1⟫_ℝ := by
    rw [← inner_neg_right]; congr 1; abel
  have e5 : ‖xk1 - xk‖ = ‖xk - xk1‖ := norm_sub_rev _ _
  rw [e5] at hd1
  set I2 := ⟪gradient f xk, xb - xk1⟫_ℝ
  set I3 := ⟪gradient f xk, xb - xk⟫_ℝ
  set I4 := ⟪gradient f xk, xk - xk1⟫_ℝ
  set I1 := ⟪xk - xk1, xk1 - xb⟫_ℝ
  set D := ‖xk - xk1‖ ^ 2
  set N := ‖xk - xb‖ ^ 2
  have hI2 : I2 ≤ f xb - f xk1 - c / 2 * N + L / 2 * D := by
    rw [e3]; linarith
  have hm := mul_le_mul_of_nonneg_left hI2 hα.le
  have hD : 0 ≤ (1 - α * L) * D := mul_nonneg (by linarith) (sq_nonneg _)
  rw [e2] at hP
  nlinarith

end NGCore

end NGSec


theorem solution {n : ℕ} (X : Set (NecoaraNG.Chain.E n)) (hXc : IsClosed X) (hXconv : Convex ℝ X)
    (f : NecoaraNG.Chain.E n → ℝ) (hf : ConvexOn ℝ X f) (hdiff : ∀ x ∈ X, DifferentiableAt ℝ f x)
    (Lf : ℝ) (hLf : 0 < Lf)
    (hL : ∀ x ∈ X, ∀ y ∈ X, ‖gradient f x - gradient f y‖ ≤ Lf * ‖x - y‖)
    (xstar : NecoaraNG.Chain.E n) (hxstar : xstar ∈ NecoaraNG.Chain.optSet X f) :
    ∀ x ∈ X, ∀ xp, NecoaraNG.ErrBound.IsPGStep X f Lf x xp → f xp ≤ f x - Lf / 2 * ‖xp - x‖ ^ 2 := by
  intro x hx xp hxp
  have h := NGCore.descent_core hXconv hdiff hL (α := 1 / Lf) (by positivity) hx hxp
  have e : 1 / (1 / Lf) = Lf := by field_simp
  rw [e] at h
  nlinarith [sq_nonneg ‖xp - x‖]

