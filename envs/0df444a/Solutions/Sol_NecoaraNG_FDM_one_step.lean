-- Prove2me | solution 1 for NecoaraNG.FDM.one_step
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T04:05:28.24326+00:00
-- url     : https://prove2.me/submissions/2e602cd2-a614-4ac4-8e86-3039b37251c8

import Mathlib
import Definitions.Def_NecoaraNG_FDM_Setting

set_option autoImplicit false

section HlpSec
open scoped InnerProductSpace
open Filter Topology

namespace Hlp
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem inner_grad_eq (f : H → ℝ) (p v : H) : ⟪gradient f p, v⟫_ℝ = fderiv ℝ f p v := by
  unfold gradient
  rw [InnerProductSpace.toDual_symm_apply]

theorem line_hasDeriv {f : H → ℝ} {p : H} (hp : DifferentiableAt ℝ f p) (x v : H) (t : ℝ)
    (hpt : x + t • v = p) :
    HasDerivAt (fun s : ℝ => f (x + s • v)) (⟪gradient f p, v⟫_ℝ) t := by
  have h1 : HasDerivAt (fun s : ℝ => x + s • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  rw [inner_grad_eq]
  subst hpt
  exact hp.hasFDerivAt.comp_hasDerivAt t h1

theorem convex_ineq {X : Set H} {f : H → ℝ} (hf : ConvexOn ℝ X f)
    (hd : ∀ x ∈ X, DifferentiableAt ℝ f x) {x y : H} (hx : x ∈ X) (hy : y ∈ X) :
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

theorem line_mem {X : Set (H)} (hX : Convex ℝ X) {x y : H} (hx : x ∈ X) (hy : y ∈ X)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) : x + t • (y - x) ∈ X := by
  have := hX hx hy (a := 1 - t) (b := t) (by linarith [ht.2]) ht.1 (by ring)
  convert this using 1
  module

theorem descent {X : Set (H)} (hX : Convex ℝ X) {f : H → ℝ}
    (hd : ∀ x ∈ X, DifferentiableAt ℝ f x) {L : ℝ}
    (hL : ∀ x ∈ X, ∀ y ∈ X, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    {x y : H} (hx : x ∈ X) (hy : y ∈ X) :
    f y ≤ f x + ⟪gradient f x, y - x⟫_ℝ + L / 2 * ‖y - x‖ ^ 2 := by
  set v := y - x with hv
  let g : ℝ → ℝ := fun s => f (x + s • v) - s * ⟪gradient f x, v⟫_ℝ - L / 2 * s ^ 2 * ‖v‖ ^ 2
  have hder : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasDerivAt g
      (⟪gradient f (x + s • v), v⟫_ℝ - ⟪gradient f x, v⟫_ℝ - L * s * ‖v‖ ^ 2) s := by
    intro s hs
    have hm := Hlp.line_mem hX hx hy hs
    have h1 := Hlp.line_hasDeriv (hd _ hm) x v s rfl
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
      have hm := Hlp.line_mem hX hx hy hs'
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

theorem cocoercive {f : H → ℝ} (hd : ∀ x, DifferentiableAt ℝ f x) {L : ℝ} (hL0 : 0 < L)
    (hL : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hc : ∀ x y, f x + ⟪gradient f x, y - x⟫_ℝ ≤ f y) (x y : H) :
    ‖gradient f y - gradient f x‖ ^ 2 ≤ 2 * L * (f y - f x - ⟪gradient f x, y - x⟫_ℝ) := by
  set d := gradient f y - gradient f x with hd'
  set z := y - (1 / L) • d with hz
  have h1 := descent (X := Set.univ) convex_univ (f := f) (fun x _ => hd x) (L := L)
    (fun x _ y _ => hL x y) (x := y) (y := z) (Set.mem_univ _) (Set.mem_univ _)
  have h2 := hc x z
  have e1 : z - y = -((1 / L) • d) := by rw [hz]; abel
  have e2 : z - x = (y - x) - (1 / L) • d := by rw [hz]; abel
  rw [e1] at h1
  rw [e2] at h2
  rw [inner_neg_right, real_inner_smul_right, norm_neg, norm_smul, mul_pow, Real.norm_eq_abs,
    sq_abs] at h1
  rw [inner_sub_right, real_inner_smul_right] at h2
  have h3 : ⟪gradient f y, d⟫_ℝ - ⟪gradient f x, d⟫_ℝ = ‖d‖ ^ 2 := by
    rw [← inner_sub_left, ← hd', real_inner_self_eq_norm_sq]
  have hq : (1 / L) * L = 1 := by field_simp
  have h4 : L * (1 / L) = 1 := by field_simp
  have key : ‖d‖ ^ 2 ≤ 2 * L * (f y - f x - ⟪gradient f x, y - x⟫_ℝ) := by
    have h5 : f x + (⟪gradient f x, y - x⟫_ℝ - 1 / L * ⟪gradient f x, d⟫_ℝ)
        ≤ f y + (-(1 / L * ⟪gradient f y, d⟫_ℝ)) + L / 2 * (1 / L ^ 2 * ‖d‖ ^ 2) := by
      have : (1 / L) ^ 2 = 1 / L ^ 2 := by rw [one_div_pow]
      rw [this] at h1
      linarith
    have h6 : 1 / L * ⟪gradient f y, d⟫_ℝ - 1 / L * ⟪gradient f x, d⟫_ℝ = 1 / L * ‖d‖ ^ 2 := by
      rw [← mul_sub, h3]
    have h7 : L / 2 * (1 / L ^ 2 * ‖d‖ ^ 2) = 1 / (2 * L) * ‖d‖ ^ 2 := by
      field_simp
    have h8 : f x + ⟪gradient f x, y - x⟫_ℝ + 1 / (2 * L) * ‖d‖ ^ 2 ≤ f y := by
      have : 1 / L * ‖d‖ ^ 2 - 1 / (2 * L) * ‖d‖ ^ 2 = 1 / (2 * L) * ‖d‖ ^ 2 := by
        field_simp; ring
      linarith
    have h9 := mul_le_mul_of_nonneg_left h8 (by linarith : (0:ℝ) ≤ 2 * L)
    have h10 : 2 * L * (1 / (2 * L) * ‖d‖ ^ 2) = ‖d‖ ^ 2 := by field_simp
    nlinarith
  exact key


theorem norm_sub_smul_sq (W g : H) (t : ℝ) :
    ‖W - t • g‖ ^ 2 = ‖W‖ ^ 2 - 2 * t * ⟪g, W⟫_ℝ + t ^ 2 * ‖g‖ ^ 2 := by
  rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    ← real_inner_comm W g]
  ring

end Hlp
end HlpSec

section NGHSec
open scoped InnerProductSpace
open NecoaraNG.Chain Filter Topology

namespace NGH
variable {n : ℕ}

theorem line_mem {X : Set (E n)} (hX : Convex ℝ X) {x y : E n} (hx : x ∈ X) (hy : y ∈ X)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) : x + t • (y - x) ∈ X := by
  have := hX hx hy (a := 1 - t) (b := t) (by linarith [ht.2]) ht.1 (by ring)
  convert this using 1
  module


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


theorem opt_val {X : Set (E n)} {f : E n → ℝ} {xstar xb : E n} (h : xstar ∈ optSet X f)
    (hb : xb ∈ optSet X f) : f xb = f xstar :=
  le_antisymm (hb.2 _ h.1) (h.2 _ hb.1)


end NGH
end NGHSec

namespace NecoaraNG.FDM
open scoped InnerProductSpace

theorem Hlp_gap {n : ℕ} (X : Set (NecoaraNG.Chain.E n)) (hXconv : Convex ℝ X)
    (f : NecoaraNG.Chain.E n → ℝ) (hf : ConvexOn ℝ X f) (hdiff : ∀ x ∈ X, DifferentiableAt ℝ f x)
    (Lf : ℝ) (hL : ∀ x ∈ X, ∀ y ∈ X, ‖gradient f x - gradient f y‖ ≤ Lf * ‖x - y‖)
    (β L Lbar : ℝ) (hβ : 0 < β) (hLbar : 0 < Lbar)
    (α : ℕ → ℝ) (e x : ℕ → NecoaraNG.Chain.E n) (hrun : IsFDMRun X f β L Lbar α e x) :
    ∀ k : ℕ, ∀ xbar ∈ X, 
      f (x (k + 1)) - f xbar ≤
        (Lf + Lbar + β * Lbar) * ‖x (k + 1) - x k‖ * ‖x (k + 1) - xbar‖ := by
  intro k xbar hxbX
  have hxX : ∀ k, x k ∈ X := by
    intro k
    cases k with
    | zero => exact hrun.1
    | succ k => exact (hrun.2 k).1.1
  obtain ⟨hnear, herr, hdesc, hα⟩ := hrun.2 k
  have haX : x (k + 1) ∈ X := hnear.1
  have hkX := hxX k
  have hc := Hlp.convex_ineq hf hdiff haX hxbX
  have hopt := NGH.proj_ineq hXconv hnear hxbX
  have hLip := hL (x (k + 1)) haX (x k) hkX
  have hα0 : 0 < α k := lt_of_lt_of_le (by positivity) hα
  have hαL : 1 ≤ α k * Lbar := by
    have := mul_le_mul_of_nonneg_right hα hLbar.le
    rwa [one_div, inv_mul_cancel₀ hLbar.ne'] at this
  set d := x (k + 1) - xbar with hd
  set g := gradient f (x k) with hg
  set ga := gradient f (x (k + 1)) with hga
  set Δn := ‖x (k + 1) - x k‖ with hΔ
  have e1 : xbar - x (k + 1) = -d := by rw [hd]; abel
  rw [e1, inner_neg_right] at hc hopt
  have e2 : x k - α k • g + e k - x (k + 1) = (x k - x (k + 1)) - α k • g + e k := by abel
  rw [e2, inner_add_left, inner_sub_left, real_inner_smul_left] at hopt
  have hb1 : inner ℝ (x k - x (k + 1)) d ≤ Δn * ‖d‖ := by
    have := real_inner_le_norm (x k - x (k + 1)) d
    rwa [norm_sub_rev] at this
  have hb2 : inner ℝ (e k) d ≤ β * Δn * ‖d‖ := by
    have := real_inner_le_norm (e k) d
    nlinarith [norm_nonneg d]
  have hb3 : inner ℝ (ga - g) d ≤ Lf * Δn * ‖d‖ := by
    have := real_inner_le_norm (ga - g) d
    nlinarith [norm_nonneg d]
  have hT : 0 ≤ (1 + β) * Δn * ‖d‖ := by positivity
  have hαG : α k * inner ℝ g d ≤ (1 + β) * Δn * ‖d‖ := by nlinarith
  have hG : inner ℝ g d ≤ Lbar * ((1 + β) * Δn * ‖d‖) := by
    rcases le_or_gt (inner ℝ g d) 0 with h | h
    · have : 0 ≤ Lbar * ((1 + β) * Δn * ‖d‖) := by positivity
      linarith
    · nlinarith [mul_nonneg (sub_nonneg.2 hαL) h.le, mul_le_mul_of_nonneg_left hαG hLbar.le]
  have hsplit : inner ℝ ga d = inner ℝ (ga - g) d + inner ℝ g d := by
    rw [inner_sub_left]; ring
  nlinarith

theorem Hlp_ineq66 {n : ℕ} (X : Set (NecoaraNG.Chain.E n)) (hXconv : Convex ℝ X)
    (f : NecoaraNG.Chain.E n → ℝ) (hf : ConvexOn ℝ X f) (hdiff : ∀ x ∈ X, DifferentiableAt ℝ f x)
    (Lf : ℝ) (hLf : 0 < Lf)
    (hL : ∀ x ∈ X, ∀ y ∈ X, ‖gradient f x - gradient f y‖ ≤ Lf * ‖x - y‖)
    (κ : ℝ) (hκ : 0 < κ) (hF : NecoaraNG.Chain.QuadFunGrowth X f κ)
    (β L Lbar : ℝ) (hβ : 0 < β) (hLbar : 0 < Lbar)
    (α : ℕ → ℝ) (e x : ℕ → NecoaraNG.Chain.E n) (hrun : IsFDMRun X f β L Lbar α e x) :
    ∀ k : ℕ, ∀ xbar, NecoaraNG.Chain.IsNearest (NecoaraNG.Chain.optSet X f) (x (k + 1)) xbar →
      f (x (k + 1)) - f xbar ≤
        2 * (Lf + Lbar + β * Lbar) ^ 2 / κ * ‖x (k + 1) - x k‖ ^ 2 := by
  intro k xbar hxbar
  have hxbX : xbar ∈ X := hxbar.1.1
  have hgap := Hlp_gap X hXconv f hf hdiff Lf hL β L Lbar hβ hLbar α e x hrun k xbar hxbX
  have haX : x (k + 1) ∈ X := (hrun.2 k).1.1
  have hq := hF _ haX xbar hxbar
  set M := Lf + Lbar + β * Lbar with hM
  have hM0 : 0 < M := by positivity
  set D := ‖x (k + 1) - xbar‖ with hD
  set Δn := ‖x (k + 1) - x k‖ with hΔ
  have hD0 : 0 ≤ D := norm_nonneg _
  have hΔ0 : 0 ≤ Δn := norm_nonneg _
  rcases hD0.eq_or_lt with h0 | hpos
  · rw [← h0] at hgap
    have : 0 ≤ 2 * M ^ 2 / κ * Δn ^ 2 := by positivity
    linarith
  · have h1 : κ / 2 * D ≤ M * Δn := by
      have : κ / 2 * D * D ≤ M * Δn * D := by nlinarith
      exact le_of_mul_le_mul_right this hpos
    have h2 : D ≤ 2 * M * Δn / κ := by
      rw [le_div_iff₀ hκ]; nlinarith
    calc f (x (k + 1)) - f xbar ≤ M * Δn * D := hgap
      _ ≤ M * Δn * (2 * M * Δn / κ) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 2 * M ^ 2 / κ * Δn ^ 2 := by field_simp

end NecoaraNG.FDM

open NecoaraNG.FDM
open scoped InnerProductSpace

theorem solution {n : ℕ} (X : Set (NecoaraNG.Chain.E n)) (hXc : IsClosed X) (hXconv : Convex ℝ X)
    (f : NecoaraNG.Chain.E n → ℝ) (hf : ConvexOn ℝ X f) (hdiff : ∀ x ∈ X, DifferentiableAt ℝ f x)
    (Lf : ℝ) (hLf : 0 < Lf)
    (hL : ∀ x ∈ X, ∀ y ∈ X, ‖gradient f x - gradient f y‖ ≤ Lf * ‖x - y‖)
    (xstar : NecoaraNG.Chain.E n) (hxstar : xstar ∈ NecoaraNG.Chain.optSet X f)
    (κ : ℝ) (hκ : 0 < κ) (hF : NecoaraNG.Chain.QuadFunGrowth X f κ)
    (β L Lbar : ℝ) (hβ : 0 < β) (hLpos : 0 < L) (hLbar : 0 < Lbar)
    (α : ℕ → ℝ) (e x : ℕ → NecoaraNG.Chain.E n) (hrun : IsFDMRun X f β L Lbar α e x) :
    ∀ k : ℕ, f (x (k + 1)) - f xstar ≤
      1 / (1 + L * κ / (4 * (Lf + Lbar + β * Lbar) ^ 2)) * (f (x k) - f xstar) := by
  intro k
  have hcl := NGH.optSet_closed hXc hdiff hxstar
  obtain ⟨xbar, hxbar⟩ := NGH.exists_nearest hcl ⟨xstar, hxstar⟩ (x (k + 1))
  have hval : f xbar = f xstar := NGH.opt_val hxstar hxbar.1
  have h66 := Hlp_ineq66 X hXconv f hf hdiff Lf hLf hL κ hκ hF β L Lbar hβ hLbar α e x hrun k xbar hxbar
  rw [hval] at h66
  have hdesc := (hrun.2 k).2.2.1
  set M := Lf + Lbar + β * Lbar with hM
  have hM0 : 0 < M := by positivity
  set Δn := ‖x (k + 1) - x k‖ with hΔ
  set r := f (x (k + 1)) - f xstar with hr
  have h1 : κ * r ≤ 2 * M ^ 2 * Δn ^ 2 := by
    have := mul_le_mul_of_nonneg_left h66 hκ.le
    have e : κ * (2 * M ^ 2 / κ * Δn ^ 2) = 2 * M ^ 2 * Δn ^ 2 := by field_simp
    linarith
  have hc : L * κ / (4 * M ^ 2) * r ≤ L / 2 * Δn ^ 2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left h1 hLpos.le]
  rw [one_div, inv_mul_eq_div, le_div_iff₀ (by positivity)]
  nlinarith
