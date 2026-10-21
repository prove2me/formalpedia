-- Prove2me | solution 1 for NecoaraNG.FGM.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T04:40:54.528876+00:00
-- url     : https://prove2.me/submissions/0ff3773f-d62b-4dcc-b0c1-1594552dedab

import Mathlib
import Definitions.Def_NecoaraNG_FGM_Setting

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

namespace NecoaraNG.FGM
open scoped InnerProductSpace

theorem Hlp_ineq54 {n : ℕ} (X : Set (NecoaraNG.Chain.E n)) (hXconv : Convex ℝ X)
    (f : NecoaraNG.Chain.E n → ℝ) (hdiff : ∀ x, DifferentiableAt ℝ f x)
    (Lf : ℝ) (hLf : 0 < Lf) (hL : ∀ x y, ‖gradient f x - gradient f y‖ ≤ Lf * ‖x - y‖)
    (κ : ℝ) (hqs : QuasiStrongEverywhere X f κ) :
    ∀ z zbar, NecoaraNG.Chain.IsNearest (NecoaraNG.Chain.optSet X f) z zbar →
      ∀ zp, NecoaraNG.Chain.IsNearest X (z - (1 / Lf) • gradient f z) zp →
        f zp + ⟪Lf • (z - zp), zbar - z⟫_ℝ + 1 / (2 * Lf) * ‖Lf • (z - zp)‖ ^ 2 +
          κ / 2 * ‖zbar - z‖ ^ 2 ≤ f zbar := by
  intro z zbar hzb zp hzp
  have hzbX : zbar ∈ X := hzb.1.1
  have hq := hqs z zbar hzb
  have hdesc := Hlp.descent (X := Set.univ) convex_univ (f := f) (fun x _ => hdiff x) (L := Lf)
    (fun x _ y _ => hL x y) (x := z) (y := zp) (Set.mem_univ _) (Set.mem_univ _)
  have hproj := NGH.proj_ineq hXconv hzp hzbX
  set a := gradient f z with ha
  set g : NecoaraNG.Chain.E n := Lf • (z - zp) with hg
  have hLne : Lf ≠ 0 := hLf.ne'
  have e1 : zp - z = -((1 / Lf) • g) := by
    rw [hg, smul_smul, one_div, inv_mul_cancel₀ hLne, one_smul]; abel
  have e2 : (z - (1 / Lf) • a) - zp = (1 / Lf) • (g - a) := by
    rw [hg, smul_sub, smul_smul, one_div, inv_mul_cancel₀ hLne, one_smul]; abel
  rw [e2, real_inner_smul_left] at hproj
  have hp2 : inner ℝ (g - a) (zbar - zp) ≤ 0 := by
    by_contra h
    push_neg at h
    have : 0 < 1 / Lf * inner ℝ (g - a) (zbar - zp) := mul_pos (by positivity) h
    linarith
  rw [inner_sub_left] at hp2
  have hz : zbar - z = (zbar - zp) + (zp - z) := by abel
  have hqa : inner ℝ a (zbar - z) = inner ℝ a (zbar - zp) - 1 / Lf * inner ℝ a g := by
    rw [hz, inner_add_right, e1, inner_neg_right, real_inner_smul_right]; ring
  have hgz : inner ℝ g (zbar - z) = inner ℝ g (zbar - zp) - 1 / Lf * ‖g‖ ^ 2 := by
    rw [hz, inner_add_right, e1, inner_neg_right, real_inner_smul_right, real_inner_self_eq_norm_sq]; ring
  have hdz : inner ℝ a (zp - z) = -(1 / Lf * inner ℝ a g) := by
    rw [e1, inner_neg_right, real_inner_smul_right]
  have hn : ‖zp - z‖ ^ 2 = (1 / Lf) ^ 2 * ‖g‖ ^ 2 := by
    rw [e1, norm_neg, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  have hc : Lf / 2 * ‖zp - z‖ ^ 2 = 1 / (2 * Lf) * ‖g‖ ^ 2 := by
    rw [hn]; field_simp
  have hnz : ‖z - zbar‖ = ‖zbar - z‖ := norm_sub_rev _ _
  rw [hnz] at hq
  have hh : 1 / (2 * Lf) * ‖g‖ ^ 2 = 1 / 2 * (1 / Lf * ‖g‖ ^ 2) := by ring
  rw [hdz, hc] at hdesc
  rw [hqa] at hq
  rw [hgz]
  linarith

theorem Hlp_lemma1 {n : ℕ} (X : Set (NecoaraNG.Chain.E n)) (hXconv : Convex ℝ X)
    (f : NecoaraNG.Chain.E n → ℝ) (hdiff : ∀ x, DifferentiableAt ℝ f x)
    (Lf : ℝ) (hLf : 0 < Lf) (hL : ∀ x y, ‖gradient f x - gradient f y‖ ≤ Lf * ‖x - y‖)
    (xstar : NecoaraNG.Chain.E n) (hxstar : xstar ∈ NecoaraNG.Chain.optSet X f)
    (κ : ℝ) (hqs : QuasiStrongEverywhere X f κ)
    (y : ℕ → NecoaraNG.Chain.E n) (ystar : NecoaraNG.Chain.E n)
    (hsame : ∀ k, NecoaraNG.Chain.IsNearest (NecoaraNG.Chain.optSet X f) (y k) ystar)
    (x : ℕ → NecoaraNG.Chain.E n)
    (hx : ∀ k, NecoaraNG.Chain.IsNearest X (y k - (1 / Lf) • gradient f (y k)) (x (k + 1)))
    (α : ℕ → ℝ) (hα : ∀ k, 0 < α k ∧ α k < 1) :
    ∀ k : ℕ, phi f Lf κ α x y k ystar ≤
      (1 - lam α k) * f xstar + lam α k * phi f Lf κ α x y 0 ystar := by
  have hval : f ystar = f xstar := NGH.opt_val hxstar (hsame 0).1
  intro k
  induction k with
  | zero => simp [lam]
  | succ k ih =>
    have h54 := Hlp_ineq54 X hXconv f hdiff Lf hLf hL κ hqs (y k) ystar (hsame k) (x (k + 1)) (hx k)
    rw [hval] at h54
    show (1 - α k) * phi f Lf κ α x y k ystar +
      α k * (f (x (k + 1)) + 1 / (2 * Lf) * ‖Lf • (y k - x (k + 1))‖ ^ 2 +
        ⟪Lf • (y k - x (k + 1)), ystar - y k⟫_ℝ + κ / 2 * ‖ystar - y k‖ ^ 2)
      ≤ (1 - lam α (k + 1)) * f xstar + lam α (k + 1) * phi f Lf κ α x y 0 ystar
    have h1 : f (x (k + 1)) + 1 / (2 * Lf) * ‖Lf • (y k - x (k + 1))‖ ^ 2 +
        ⟪Lf • (y k - x (k + 1)), ystar - y k⟫_ℝ + κ / 2 * ‖ystar - y k‖ ^ 2 ≤ f xstar := by
      linarith
    have h0 := (hα k).1
    have h2 : 0 ≤ 1 - α k := by linarith [(hα k).2]
    have h3 := mul_le_mul_of_nonneg_left ih h2
    have h4 := mul_le_mul_of_nonneg_left h1 h0.le
    have e : lam α (k + 1) = (1 - α k) * lam α k := rfl
    rw [e]
    nlinarith

end NecoaraNG.FGM

open NecoaraNG.FGM
open scoped InnerProductSpace

theorem solution {n : ℕ} (X : Set (NecoaraNG.Chain.E n)) (hXc : IsClosed X) (hXconv : Convex ℝ X)
    (f : NecoaraNG.Chain.E n → ℝ) (hdiff : ∀ x, DifferentiableAt ℝ f x) (hf : ConvexOn ℝ Set.univ f)
    (Lf : ℝ) (hLf : 0 < Lf) (hL : ∀ x y, ‖gradient f x - gradient f y‖ ≤ Lf * ‖x - y‖)
    (xstar : NecoaraNG.Chain.E n) (hxstar : xstar ∈ NecoaraNG.Chain.optSet X f)
    (κ : ℝ) (hκ : 0 < κ) (hqs : QuasiStrongEverywhere X f κ)
    (y : ℕ → NecoaraNG.Chain.E n) (ystar : NecoaraNG.Chain.E n) (hsame : ∀ k, NecoaraNG.Chain.IsNearest (NecoaraNG.Chain.optSet X f) (y k) ystar)
    (x : ℕ → NecoaraNG.Chain.E n) (hx0 : x 0 = y 0)
    (hx : ∀ k, NecoaraNG.Chain.IsNearest X (y k - (1 / Lf) • gradient f (y k)) (x (k + 1)))
    (α : ℕ → ℝ) (hα : ∀ k, 0 < α k ∧ α k < 1)
    (hmin : ∀ k z, f (x k) ≤ phi f Lf κ α x y k z) :
    ∀ k : ℕ, f (x k) - f xstar ≤
      lam α k * (f (x 0) - f xstar + κ / 2 * ‖ystar - y 0‖ ^ 2) := by
  intro k
  have h1 := Hlp_lemma1 X hXconv f hdiff Lf hLf hL xstar hxstar κ hqs y ystar hsame x hx α hα k
  have h2 := hmin k ystar
  have h3 : phi f Lf κ α x y 0 ystar = f (y 0) + κ / 2 * ‖ystar - y 0‖ ^ 2 := rfl
  rw [h3, ← hx0] at h1
  rw [← hx0]
  nlinarith
