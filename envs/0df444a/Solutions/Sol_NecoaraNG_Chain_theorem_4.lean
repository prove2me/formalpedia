-- Prove2me | solution 1 for NecoaraNG.Chain.theorem_4
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-09T18:53:18.052174+00:00
-- url     : https://prove2.me/submissions/e5719a5c-5365-4a00-82f1-0cd8c92ac138

import Mathlib
import Definitions.Def_NecoaraNG_Chain_Setting

open scoped InnerProductSpace

namespace RRAux_NecoaraNG_Chain_theorem_4

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
theorem line_hasDerivAt {φ : F → ℝ} {x v : F} {t : ℝ} (h : DifferentiableAt ℝ φ (x + t • v)) :
    HasDerivAt (fun s : ℝ => φ (x + s • v)) ⟪gradient φ (x + t • v), v⟫_ℝ t := by
  have h1 : HasDerivAt (fun s : ℝ => x + s • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  have h2 := h.hasGradientAt.hasFDerivAt.comp_hasDerivAt t h1
  have h3 : HasDerivAt (fun s : ℝ => φ (x + s • v))
      ((InnerProductSpace.toDual ℝ F (gradient φ (x + t • v))) v) t := h2
  rwa [InnerProductSpace.toDual_apply_apply] at h3

theorem convex_line {S : Set F} {φ : F → ℝ} (hφ : ConvexOn ℝ S φ) {x y : F} (hx : x ∈ S)
    (hy : y ∈ S) : ConvexOn ℝ (Set.Icc 0 1) (fun s : ℝ => φ (x + s • (y - x))) := by
  refine ⟨convex_Icc 0 1, ?_⟩
  intro a ha b hb α β hα hβ hαβ
  have h := hφ.2 (hφ.1.add_smul_sub_mem hx hy ha) (hφ.1.add_smul_sub_mem hx hy hb) hα hβ hαβ
  obtain rfl : β = 1 - α := by linarith
  have he : x + (α * a + (1 - α) * b) • (y - x)
      = α • (x + a • (y - x)) + (1 - α) • (x + b • (y - x)) := by module
  simpa [he] using h

theorem convex_first_order_line {S : Set F} {φ : F → ℝ} (hφ : ConvexOn ℝ S φ) {x y : F}
    (hx : x ∈ S) (hy : y ∈ S) {D : ℝ}
    (hD : HasDerivAt (fun s : ℝ => φ (x + s • (y - x))) D 0) : φ x + D ≤ φ y := by
  have h := (convex_line hφ hx hy).le_slope_of_hasDerivAt (x := 0) (y := 1)
    (by simp) (by simp) one_pos hD
  rw [slope_def_field] at h
  simp at h
  linarith

theorem convex_first_order {S : Set F} {φ : F → ℝ} (hφ : ConvexOn ℝ S φ) {x y : F}
    (hx : x ∈ S) (hy : y ∈ S) (hd : DifferentiableAt ℝ φ x) :
    φ x + ⟪gradient φ x, y - x⟫_ℝ ≤ φ y := by
  have hd' : DifferentiableAt ℝ φ (x + (0:ℝ) • (y - x)) := by simpa using hd
  have := line_hasDerivAt hd'
  simp only [zero_smul, add_zero] at this
  exact convex_first_order_line hφ hx hy this

theorem deriv_nonneg_of_min {φ : ℝ → ℝ} {D : ℝ} (hD : HasDerivAt φ D 0)
    (hmin : ∀ t ∈ Set.Ioo (0:ℝ) 1, φ 0 ≤ φ t) : 0 ≤ D := by
  have ht := hD.tendsto_slope_zero_right
  apply ge_of_tendsto ht
  have : Set.Ioo (0:ℝ) 1 ∈ nhdsWithin (0:ℝ) (Set.Ioi 0) := Ioo_mem_nhdsGT one_pos
  filter_upwards [this] with t htm
  simp only [zero_add, smul_eq_mul]
  exact mul_nonneg (inv_nonneg.mpr htm.1.le) (sub_nonneg.mpr (hmin t htm))

theorem eps_limit (a b K : ℝ) (hK : 0 ≤ K)
    (h : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → b - ε * K ≤ a) : b ≤ a := by
  by_contra hc
  have hδ : 0 < b - a := by linarith [not_le.mp hc]
  set δ := b - a
  set ε := δ / (δ + K)
  have hpos : 0 < δ + K := by linarith
  have hε : ε * (δ + K) = δ := by simp only [ε]; field_simp
  have hεpos : 0 < ε := div_pos hδ hpos
  have hε1 : ε ≤ 1 := by rw [div_le_one hpos]; linarith
  have := h ε hεpos hε1
  nlinarith [mul_pos hεpos hδ]

end RRAux_NecoaraNG_Chain_theorem_4

namespace RRAux_NecoaraNG_Chain_theorem_4
open NecoaraNG.Chain

theorem near_seg {n : ℕ} {S : Set (E n)} {x xb : E n} (h : IsNearest S x xb) {τ : ℝ}
    (hτ : τ ∈ Set.Icc (0:ℝ) 1) : IsNearest S (xb + τ • (x - xb)) xb := by
  refine ⟨h.1, fun z hz => ?_⟩
  have h1 := h.2 z hz
  have e1 : xb + τ • (x - xb) - xb = τ • (x - xb) := by abel
  have e2 : x - (xb + τ • (x - xb)) = (1 - τ) • (x - xb) := by module
  have tri := norm_sub_le_norm_sub_add_norm_sub x (xb + τ • (x - xb)) z
  rw [e1, norm_smul, Real.norm_eq_abs, abs_of_nonneg hτ.1]
  rw [e2, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith [hτ.2])] at tri
  nlinarith

theorem under_of_QS {n : ℕ} {X : Set (E n)} (hXconv : Convex ℝ X)
    {f : E n → ℝ} (hf : ConvexOn ℝ X f) (hdiff : ∀ x ∈ X, DifferentiableAt ℝ f x)
    {κ : ℝ} (hκ : 0 < κ) (hQS : QuasiStrong X f κ) {x xb : E n} (hx : x ∈ X)
    (hxb : IsNearest (optSet X f) x xb) :
    f xb + ⟪gradient f xb, x - xb⟫_ℝ + κ / 2 * ‖x - xb‖ ^ 2 ≤ f x := by
  have hxbX : xb ∈ X := hxb.1.1
  set v := x - xb with hv
  set d2 := ‖v‖ ^ 2 with hd2
  set c := ⟪gradient f xb, v⟫_ℝ with hc
  set fs := f xb with hfs
  have hmem : ∀ τ ∈ Set.Icc (0:ℝ) 1, xb + τ • v ∈ X := fun τ hτ =>
    hXconv.add_smul_sub_mem hxbX hx hτ
  have hd2nn : 0 ≤ d2 := by positivity
  -- QS along the segment
  have hstar : ∀ τ ∈ Set.Icc (0:ℝ) 1, f (xb + τ • v) - τ * ⟪gradient f (xb + τ • v), v⟫_ℝ
      + κ / 2 * (τ ^ 2 * d2) ≤ fs := by
    intro τ hτ
    have h := hQS _ (hmem τ hτ) xb (near_seg hxb hτ)
    have e1 : xb - (xb + τ • v) = -(τ • v) := by abel
    have e2 : xb + τ • v - xb = τ • v := by abel
    rw [e1, e2, inner_neg_right, inner_smul_right, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hτ.1, mul_pow] at h
    linarith
  have hx1 : xb + (1:ℝ) • v = x := by rw [one_smul, hv]; abel
  have key : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → c - ε * (κ / 2 * d2) ≤ f x - fs - κ / 2 * d2 := by
    intro ε hε0 hε1
    let h : ℝ → ℝ := fun τ => (f (xb + τ • v) - fs) / τ - κ / 2 * τ * d2
    have hmono : MonotoneOn h (Set.Icc ε 1) := by
      have hder : ∀ τ ∈ Set.Icc ε 1, HasDerivAt h
          ((⟪gradient f (xb + τ • v), v⟫_ℝ * τ - (f (xb + τ • v) - fs) * 1) / τ ^ 2
            - κ / 2 * d2) τ := by
        intro τ hτ
        have hτ' : τ ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith [hτ.1], hτ.2⟩
        have h1 := (line_hasDerivAt (hdiff _ (hmem τ hτ'))).sub_const fs
        have h2 := h1.div (hasDerivAt_id' τ) (by linarith [hτ.1])
        have h3 := ((hasDerivAt_id' τ).const_mul (κ / 2)).mul_const d2
        have h4 := h2.sub h3
        rw [show κ / 2 * 1 * d2 = κ / 2 * d2 by ring] at h4
        exact h4
      apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc ε 1)
      · intro τ hτ; exact (hder τ hτ).continuousAt.continuousWithinAt
      · intro τ hτ; exact (hder τ (interior_subset hτ)).hasDerivWithinAt
      · intro τ hτ
        rw [interior_Icc] at hτ
        have hτ0 : 0 < τ := by linarith [hτ.1]
        have hs := hstar τ ⟨hτ0.le, hτ.2.le⟩
        have hτ2 : 0 < τ ^ 2 := by positivity
        rw [sub_nonneg, le_div_iff₀ hτ2]
        nlinarith
    have hle := hmono ⟨le_rfl, hε1⟩ ⟨hε1, le_rfl⟩ hε1
    simp only [h, div_one, one_mul, hx1] at hle
    -- lower bound for h ε
    have hcv := convex_first_order hf hxbX (hmem ε ⟨hε0.le, hε1⟩) (hdiff xb hxbX)
    have e3 : xb + ε • v - xb = ε • v := by abel
    rw [e3, inner_smul_right] at hcv
    have hlow : c ≤ (f (xb + ε • v) - fs) / ε := by
      rw [le_div_iff₀ hε0]; linarith
    linarith
  have := eps_limit (f x - fs - κ / 2 * d2) c (κ / 2 * d2) (by positivity) key
  linarith

theorem under_of_QGG {n : ℕ} {X : Set (E n)} (hXconv : Convex ℝ X)
    {f : E n → ℝ} (hdiff : ∀ x ∈ X, DifferentiableAt ℝ f x)
    {κ : ℝ} (hQ : QuadGradGrowth X f κ) {x xb : E n} (hx : x ∈ X)
    (hxb : IsNearest (optSet X f) x xb) :
    f xb + ⟪gradient f xb, x - xb⟫_ℝ + κ / 2 * ‖x - xb‖ ^ 2 ≤ f x := by
  have hxbX : xb ∈ X := hxb.1.1
  set v := x - xb with hv
  set d2 := ‖v‖ ^ 2 with hd2
  set c := ⟪gradient f xb, v⟫_ℝ with hc
  have hmem : ∀ τ ∈ Set.Icc (0:ℝ) 1, xb + τ • v ∈ X := fun τ hτ =>
    hXconv.add_smul_sub_mem hxbX hx hτ
  let g : ℝ → ℝ := fun τ => f (xb + τ • v) - τ * c - κ / 2 * τ ^ 2 * d2
  have hder : ∀ τ ∈ Set.Icc (0:ℝ) 1, HasDerivAt g
      (⟪gradient f (xb + τ • v), v⟫_ℝ - c - κ * τ * d2) τ := by
    intro τ hτ
    have h1 := line_hasDerivAt (hdiff _ (hmem τ hτ))
    have h2 := (hasDerivAt_id τ).mul_const c
    have h3 := ((hasDerivAt_pow 2 τ).const_mul (κ / 2)).mul_const d2
    have h4 := (h1.sub h2).sub h3
    have e : ⟪gradient f (xb + τ • v), v⟫_ℝ - 1 * c - κ / 2 * ((2:ℕ) * τ ^ (2 - 1)) * d2
        = ⟪gradient f (xb + τ • v), v⟫_ℝ - c - κ * τ * d2 := by push_cast; ring
    rw [e] at h4
    exact h4
  have hmono : MonotoneOn g (Set.Icc 0 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1)
    · intro τ hτ; exact (hder τ hτ).continuousAt.continuousWithinAt
    · intro τ hτ; exact (hder τ (interior_subset hτ)).hasDerivWithinAt
    · intro τ hτ
      rw [interior_Icc] at hτ
      have hτ' : τ ∈ Set.Icc (0:ℝ) 1 := ⟨hτ.1.le, hτ.2.le⟩
      have h := hQ _ (hmem τ hτ') xb (near_seg hxb hτ')
      have e2 : xb + τ • v - xb = τ • v := by abel
      rw [e2, norm_smul, Real.norm_eq_abs, abs_of_nonneg hτ'.1, mul_pow, inner_smul_right,
        inner_sub_left] at h
      have hτ0 : 0 < τ := hτ.1
      have : τ * (κ * τ * d2) ≤ τ * (⟪gradient f (xb + τ • v), v⟫_ℝ - c) := by
        rw [hd2]; nlinarith
      have := le_of_mul_le_mul_left this hτ0
      linarith
  have hle := hmono ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ zero_le_one
  have hx1 : xb + (1:ℝ) • v = x := by rw [one_smul, hv]; abel
  simp only [g, zero_smul, add_zero, zero_mul, mul_zero, sub_zero, one_mul, mul_one,
    one_pow, hx1, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at hle
  linarith

theorem grad_nonneg {n : ℕ} {X : Set (E n)} (hXconv : Convex ℝ X)
    {f : E n → ℝ} (hdiff : ∀ x ∈ X, DifferentiableAt ℝ f x) {x xb : E n} (hx : x ∈ X)
    (hxb : xb ∈ optSet X f) : 0 ≤ ⟪gradient f xb, x - xb⟫_ℝ := by
  have hd : DifferentiableAt ℝ f (xb + (0:ℝ) • (x - xb)) := by simpa using hdiff xb hxb.1
  have h := line_hasDerivAt hd
  simp only [zero_smul, add_zero] at h
  apply deriv_nonneg_of_min h
  intro t ht
  simp only [zero_smul, add_zero]
  exact hxb.2 _ (hXconv.add_smul_sub_mem hxb.1 hx ⟨ht.1.le, ht.2.le⟩)

end RRAux_NecoaraNG_Chain_theorem_4

open RRAux_NecoaraNG_Chain_theorem_4 in
open NecoaraNG.Chain in
theorem solution {n : ℕ} (X : Set (E n)) (hXc : IsClosed X) (hXconv : Convex ℝ X)
    (f : E n → ℝ) (hf : ConvexOn ℝ X f) (hdiff : ∀ x ∈ X, DifferentiableAt ℝ f x)
    (Lf : ℝ) (hLf : 0 < Lf)
    (hL : ∀ x ∈ X, ∀ y ∈ X, ‖gradient f x - gradient f y‖ ≤ Lf * ‖x - y‖)
    (xstar : E n) (hxstar : xstar ∈ optSet X f) (κ : ℝ) (hκ : 0 < κ) :
    (StrongIneq X f κ → QuasiStrong X f κ) ∧
      (QuasiStrong X f κ → QuadGradGrowth X f κ) ∧
      (QuadGradGrowth X f κ → QuadUnder X f κ) ∧
      (QuadUnder X f κ → QuadFunGrowth X f κ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hS x hx xbar hxb
    exact hS x hx xbar hxb.1.1
  · intro hQS x hx xbar hxb
    have hU := under_of_QS hXconv hf hdiff hκ hQS hx hxb
    have hQ := hQS x hx xbar hxb
    have e : xbar - x = -(x - xbar) := by abel
    rw [e, inner_neg_right] at hQ
    rw [inner_sub_left]
    linarith
  · intro hQ x hx xbar hxb
    exact under_of_QGG hXconv hdiff hQ hx hxb
  · intro hU x hx xbar hxb
    have h := hU x hx xbar hxb
    have h0 := grad_nonneg hXconv hdiff hx hxb.1
    linarith

#print axioms solution
