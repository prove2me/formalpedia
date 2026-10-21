-- Prove2me | solution 1 for NecoaraNG.GMIff.ineq_52
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T22:52:31.602994+00:00
-- url     : https://prove2.me/submissions/e1b887e6-97f1-4114-b38e-12b239887dc4

import Mathlib
import Definitions.Def_NecoaraNG_GMIff_Setting

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

section NGSec2
open NecoaraNG.Chain Filter Topology

namespace NGCore
variable {n : ℕ}

theorem ineq52_core {X : Set (E n)} (hX : Convex ℝ X) {f : E n → ℝ} (hf : ConvexOn ℝ X f)
    (hd : ∀ x ∈ X, DifferentiableAt ℝ f x) {L : ℝ}
    (hL : ∀ x ∈ X, ∀ y ∈ X, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    {xstar : E n} (hxs : xstar ∈ optSet X f) {κ : ℝ} (hF : QuadFunGrowth X f κ)
    {α : ℝ} (hα : 0 < α) (hαL : α * L ≤ 1) {xk : E n} (hxk : xk ∈ X) {xk1 : E n}
    (hn : IsNearest X (xk - α • gradient f xk) xk1) {xkb : E n}
    (hb : IsNearest (optSet X f) xk xkb) {xk1b : E n} (hb1 : IsNearest (optSet X f) xk1 xk1b) :
    (1 + κ * α) * ‖xk1 - xk1b‖ ^ 2 ≤ ‖xk - xkb‖ ^ 2 := by
  have hxb : xkb ∈ X := hb.1.1
  have h := step_ineq hX hd hL hα hαL hxk hn hxb 0
    (by have := convex_ineq hf hd hxk hxb; rw [zero_div, zero_mul, sub_zero]; linarith)
  rw [mul_zero, sub_zero, one_mul] at h
  have hq := hF xk1 hn.1 xk1b hb1
  have hv : f xk1b = f xkb := (opt_val hxs hb1.1).trans (opt_val hxs hb.1).symm
  have hm : ‖xk1 - xk1b‖ ≤ ‖xk1 - xkb‖ := hb1.2 _ hb.1
  have hm2 : ‖xk1 - xk1b‖ ^ 2 ≤ ‖xk1 - xkb‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hm 2
  have hp := mul_le_mul_of_nonneg_left hq hα.le
  rw [hv] at hp
  nlinarith

theorem ineq26_core {X : Set (E n)} (hXc : IsClosed X) (hX : Convex ℝ X) {f : E n → ℝ}
    (hd : ∀ x ∈ X, DifferentiableAt ℝ f x) {xstar : E n} (hxs : xstar ∈ optSet X f)
    {Lf β : ℝ}
    (hcontr : ∀ x ∈ X, ∀ xbar, IsNearest (optSet X f) x xbar →
      ∀ xp, NecoaraNG.ErrBound.IsPGStep X f Lf x xp →
      ∀ xpbar, IsNearest (optSet X f) xp xpbar → ‖xp - xpbar‖ ≤ β * ‖x - xbar‖)
    {x : E n} (hx : x ∈ X) {xbar : E n} (hb : IsNearest (optSet X f) x xbar) {xp : E n}
    (hp : NecoaraNG.ErrBound.IsPGStep X f Lf x xp) :
    (1 - β) * ‖x - xbar‖ ≤ ‖x - xp‖ := by
  obtain ⟨xpb, hpb⟩ := exists_nearest (optSet_closed hXc hd hxs) ⟨xstar, hxs⟩ xp
  have h1 := hcontr x hx xbar hb xp hp xpb hpb
  have h2 : ‖x - xbar‖ ≤ ‖x - xpb‖ := hb.2 _ hpb.1
  have h3 : ‖x - xpb‖ ≤ ‖x - xp‖ + ‖xp - xpb‖ := norm_sub_le_norm_sub_add_norm_sub x xp xpb
  linarith

theorem qs_growth {X : Set (E n)} (hX : Convex ℝ X) {f : E n → ℝ}
    (hd : ∀ x ∈ X, DifferentiableAt ℝ f x) {κ : ℝ} (hqs : QuasiStrong X f κ) :
    QuadFunGrowth X f κ := by
  intro x hx xb hb
  have hxb : xb ∈ X := hb.1.1
  set v := x - xb with hv
  set r := ‖v‖ with hr
  let φ : ℝ → ℝ := fun t => f (xb + t • v) - f xb
  have hmem : ∀ t ∈ Set.Icc (0 : ℝ) 1, xb + t • v ∈ X := fun t ht => line_mem hX hxb hx ht
  have hφ : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt φ (⟪gradient f (xb + t • v), v⟫_ℝ) t :=
    fun t ht => (line_hasDeriv (hd _ (hmem t ht)) xb v t rfl).sub_const (f xb)
  have hφnn : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ φ t := fun t ht => by
    have := hb.1.2 _ (hmem t ht)
    simp only [φ]; linarith
  have hnear : ∀ t ∈ Set.Ioc (0 : ℝ) 1, IsNearest (optSet X f) (xb + t • v) xb := by
    intro t ht
    refine ⟨hb.1, fun z hz => ?_⟩
    have e1 : xb + t • v - xb = t • v := by abel
    have e2 : x - (xb + t • v) = (1 - t) • v := by rw [hv]; module
    have n1 : ‖xb + t • v - xb‖ = t * r := by
      rw [e1, norm_smul, Real.norm_eq_abs, abs_of_pos ht.1]
    have n2 : ‖x - (xb + t • v)‖ = (1 - t) * r := by
      rw [e2, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith [ht.2])]
    have h1 : ‖x - z‖ ≤ ‖x - (xb + t • v)‖ + ‖(xb + t • v) - z‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    have h2 : r ≤ ‖x - z‖ := hb.2 z hz
    rw [n1]
    rw [n2] at h1
    nlinarith
  have hkey : ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      φ t + κ / 2 * (t * r) ^ 2 ≤ t * ⟪gradient f (xb + t • v), v⟫_ℝ := by
    intro t ht
    have hI : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
    have h := hqs _ (hmem t hI) xb (hnear t ht)
    have e1 : xb + t • v - xb = t • v := by abel
    have n1 : ‖xb + t • v - xb‖ = t * r := by
      rw [e1, norm_smul, Real.norm_eq_abs, abs_of_pos ht.1]
    have e3 : xb - (xb + t • v) = -(t • v) := by abel
    rw [e3, inner_neg_right, real_inner_smul_right, n1] at h
    simp only [φ]
    linarith
  let h : ℝ → ℝ := fun t => φ t / t - κ * r ^ 2 / 2 * t
  have hh : ∀ t ∈ Set.Ioc (0 : ℝ) 1, HasDerivAt h
      ((⟪gradient f (xb + t • v), v⟫_ℝ * t - φ t) / t ^ 2 - κ * r ^ 2 / 2) t := by
    intro t ht
    have hI : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
    have h1 := (hφ t hI).div (hasDerivAt_id t) ht.1.ne'
    have h2 := (hasDerivAt_id t).const_mul (κ * r ^ 2 / 2)
    refine (h1.sub h2).congr_deriv ?_
    simp
  have hmono : MonotoneOn h (Set.Ioc 0 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioc 0 1)
    · intro t ht; exact (hh t ht).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Ioc] at ht
      exact (hh t (Set.Ioo_subset_Ioc_self ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ioc] at ht
      have ht' := Set.Ioo_subset_Ioc_self ht
      rw [(hh t ht').deriv]
      have := hkey t ht'
      have hp : 0 < t ^ 2 := pow_pos ht.1 2
      have : κ * r ^ 2 / 2 ≤ (⟪gradient f (xb + t • v), v⟫_ℝ * t - φ t) / t ^ 2 := by
        rw [le_div_iff₀ hp]; nlinarith
      linarith
  have hlim : ∀ ε ∈ Set.Ioo (0 : ℝ) 1, κ / 2 * r ^ 2 * (1 - ε) ≤ φ 1 := by
    intro ε hε
    have hle := hmono ⟨hε.1, hε.2.le⟩ ⟨one_pos, le_rfl⟩ hε.2.le
    simp only [h] at hle
    have h0 : 0 ≤ φ ε / ε := div_nonneg (hφnn ε ⟨hε.1.le, hε.2.le⟩) hε.1.le
    simp only [div_one, mul_one] at hle
    nlinarith
  have hfin : κ / 2 * r ^ 2 ≤ φ 1 := by
    have ht : Filter.Tendsto (fun ε : ℝ => κ / 2 * r ^ 2 * (1 - ε)) (𝓝[>] 0)
        (𝓝 (κ / 2 * r ^ 2 * (1 - 0))) :=
      ((continuous_const.mul (continuous_const.sub continuous_id)).tendsto 0).mono_left
        nhdsWithin_le_nhds
    have := le_of_tendsto ht (by
      filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with ε hε using hlim ε hε)
    simpa using this
  have e : xb + (1 : ℝ) • v = x := by simp [hv]
  simp only [φ, e] at hfin
  exact hfin

end NGCore
end NGSec2

theorem solution (n : ℕ) (X : Set (NecoaraNG.Chain.E n)) (hXc : IsClosed X) (hXconv : Convex ℝ X)
    (f : NecoaraNG.Chain.E n → ℝ) (hf : ConvexOn ℝ X f)
    (hdiff : ∀ x ∈ X, DifferentiableAt ℝ f x)
    (Lf : ℝ) (hLf : 0 < Lf)
    (hL : ∀ x ∈ X, ∀ y ∈ X, ‖gradient f x - gradient f y‖ ≤ Lf * ‖x - y‖)
    (xstar : NecoaraNG.Chain.E n) (hxstar : xstar ∈ NecoaraNG.Chain.optSet X f)
    (κ : ℝ) (hκ : 0 < κ) (hF : NecoaraNG.Chain.QuadFunGrowth X f κ)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1 / Lf) :
    ∀ xk ∈ X, ∀ xk1, NecoaraNG.Chain.IsNearest X (xk - α • gradient f xk) xk1 →
      ∀ xkbar, NecoaraNG.Chain.IsNearest (NecoaraNG.Chain.optSet X f) xk xkbar →
      ∀ xk1bar, NecoaraNG.Chain.IsNearest (NecoaraNG.Chain.optSet X f) xk1 xk1bar →
        ‖xk1 - xk1bar‖ ^ 2 ≤ 1 / (1 + κ * α) * ‖xk - xkbar‖ ^ 2 := by
  intro xk hxk xk1 hn xkb hb xk1b hb1
  have hαL : α * Lf ≤ 1 := (le_div_iff₀ hLf).1 hα1
  have h := NGCore.ineq52_core hXconv hf hdiff hL hxstar hF hα0 hαL hxk hn hb hb1
  rw [one_div, inv_mul_eq_div, le_div_iff₀ (by positivity)]
  nlinarith

