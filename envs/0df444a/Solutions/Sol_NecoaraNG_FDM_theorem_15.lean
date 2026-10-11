-- Prove2me | solution 1 for NecoaraNG.FDM.theorem_15
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T22:24:32.778595+00:00
-- url     : https://prove2.me/submissions/42c87e35-a39c-4971-9c65-300e31022631

import Mathlib
import Definitions.Def_NecoaraNG_FDM_Setting

namespace RRAux_NecoaraNG_FDM_theorem_15

open scoped InnerProductSpace

section
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

theorem grad_inner (f : F → ℝ) (x v : F) :
    fderiv ℝ f x v = ⟪gradient f x, v⟫_ℝ := by
  unfold gradient; exact InnerProductSpace.toDual_symm_apply.symm

theorem line_deriv (f : F → ℝ) (x w : F) (t : ℝ) (hd : DifferentiableAt ℝ f (x + t • w)) :
    HasDerivAt (fun s : ℝ => f (x + s • w)) ⟪gradient f (x + t • w), w⟫_ℝ t := by
  have hl : HasDerivAt (fun s : ℝ => x + s • w) w t := by
    simpa using ((hasDerivAt_id t).smul_const w).const_add x
  have hc := hd.hasFDerivAt.comp_hasDerivAt t hl
  rw [grad_inner f] at hc
  exact hc

theorem first_order {X : Set F} (hXconv : Convex ℝ X) (f : F → ℝ) (hf : ConvexOn ℝ X f)
    (hdiff : ∀ x ∈ X, DifferentiableAt ℝ f x) {x y : F} (hx : x ∈ X) (hy : y ∈ X) :
    f x + ⟪gradient f x, y - x⟫_ℝ ≤ f y := by
  set φ : ℝ → ℝ := fun t => f (x + t • (y - x)) with hφ
  have hmem : ∀ t ∈ Set.Icc (0:ℝ) 1, x + t • (y - x) ∈ X := fun t ht =>
    hXconv.add_smul_sub_mem hx hy ht
  have hconv : ConvexOn ℝ (Set.Icc (0:ℝ) 1) φ := by
    refine ⟨convex_Icc 0 1, ?_⟩
    intro a ha b hb α β hα hβ hαβ
    have := hf.2 (hmem a ha) (hmem b hb) hα hβ hαβ
    have e : α • (x + a • (y - x)) + β • (x + b • (y - x))
        = x + (α • a + β • b) • (y - x) := by
      have : α • (x + a • (y - x)) + β • (x + b • (y - x))
          = (α + β) • x + (α * a + β * b) • (y - x) := by module
      rw [this, hαβ, one_smul, smul_eq_mul, smul_eq_mul]
    rw [e] at this
    simpa [hφ] using this
  have hd : HasDerivAt φ ⟪gradient f x, y - x⟫_ℝ 0 := by
    have := line_deriv f x (y - x) 0 (by simpa using hdiff x hx)
    simpa using this
  have := hconv.le_slope_of_hasDerivAt (by simp) (by simp) zero_lt_one hd
  have e1 : φ 1 = f y := by simp only [hφ, one_smul]; congr 1; abel
  have e0 : φ 0 = f x := by simp only [hφ, zero_smul, add_zero]
  rw [slope_def_field, e1, e0, sub_zero, div_one] at this
  linarith

end

open NecoaraNG.Chain in
theorem proj_vi {n : ℕ} {S : Set (E n)} (hS : Convex ℝ S) {y p : E n} (h : IsNearest S y p) :
    ∀ z ∈ S, ⟪y - p, z - p⟫_ℝ ≤ 0 := by
  have hbdd : BddBelow (Set.range fun w : S => ‖y - (w : E n)‖) :=
    ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩
  have heq : ‖y - p‖ = ⨅ w : S, ‖y - (w : E n)‖ := by
    apply le_antisymm
    · haveI : Nonempty S := ⟨⟨p, h.1⟩⟩
      exact le_ciInf fun w => h.2 w w.2
    · exact ciInf_le hbdd ⟨p, h.1⟩
  exact (norm_eq_iInf_iff_real_inner_le_zero hS h.1).1 heq

open NecoaraNG.Chain in
theorem exists_nearest {n : ℕ} {S : Set (E n)} (hne : S.Nonempty) (hc : IsClosed S)
    (hcv : Convex ℝ S) (u : E n) : ∃ p, IsNearest S u p := by
  obtain ⟨v, hv, heq⟩ := exists_norm_eq_iInf_of_complete_convex hne hc.isComplete hcv u
  have hbdd : BddBelow (Set.range fun w : S => ‖u - (w : E n)‖) :=
    ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩
  exact ⟨v, hv, fun z hz => heq ▸ ciInf_le hbdd ⟨z, hz⟩⟩

theorem num_step (δ δk C L κ Δ r : ℝ) (hC : 0 < C) (hL : 0 < L) (hκ : 0 < κ) (hδ : 0 ≤ δ)
    (hΔ : 0 ≤ Δ) (hr : 0 ≤ r) (h1 : δ ≤ C * Δ * r) (h2 : κ / 2 * r ^ 2 ≤ δ)
    (h3 : δ ≤ δk - L / 2 * Δ ^ 2) :
    δ ≤ 1 / (1 + L * κ / (4 * C ^ 2)) * δk := by
  have hC2 : 0 < 4 * C ^ 2 := by positivity
  have e : 1 / (1 + L * κ / (4 * C ^ 2)) * δk = 4 * C ^ 2 * δk / (4 * C ^ 2 + L * κ) := by
    field_simp
  rw [e, le_div_iff₀ (by positivity)]
  have hsq : δ ^ 2 ≤ C ^ 2 * Δ ^ 2 * r ^ 2 := by
    have : δ ^ 2 ≤ (C * Δ * r) ^ 2 := pow_le_pow_left₀ hδ h1 2
    nlinarith
  have hA : L * Δ ^ 2 ≤ 2 * (δk - δ) := by linarith
  have hB : κ * r ^ 2 ≤ 2 * δ := by linarith
  have hprod : (L * Δ ^ 2) * (κ * r ^ 2) ≤ (2 * (δk - δ)) * (2 * δ) :=
    mul_le_mul hA hB (by positivity) (by linarith [sq_nonneg Δ, mul_nonneg hL.le (sq_nonneg Δ)])
  have hm : L * κ * δ ^ 2 ≤ 4 * C ^ 2 * (δk - δ) * δ := by
    have := mul_le_mul_of_nonneg_left hsq (mul_nonneg hL.le hκ.le)
    nlinarith
  rcases eq_or_lt_of_le hδ with h0 | h0
  · rw [← h0]; nlinarith [sq_nonneg Δ, mul_nonneg hL.le (sq_nonneg Δ)]
  · have : L * κ * δ ≤ 4 * C ^ 2 * (δk - δ) := by
      by_contra hc
      push Not at hc
      have := mul_lt_mul_of_pos_right hc h0
      nlinarith
    nlinarith

end RRAux_NecoaraNG_FDM_theorem_15

open scoped InnerProductSpace
open RRAux_NecoaraNG_FDM_theorem_15

open NecoaraNG.FDM in
theorem solution {n : ℕ} (X : Set (NecoaraNG.Chain.E n)) (hXc : IsClosed X) (hXconv : Convex ℝ X)
    (f : NecoaraNG.Chain.E n → ℝ) (hf : ConvexOn ℝ X f) (hdiff : ∀ x ∈ X, DifferentiableAt ℝ f x)
    (Lf : ℝ) (hLf : 0 < Lf)
    (hL : ∀ x ∈ X, ∀ y ∈ X, ‖gradient f x - gradient f y‖ ≤ Lf * ‖x - y‖)
    (xstar : NecoaraNG.Chain.E n) (hxstar : xstar ∈ NecoaraNG.Chain.optSet X f)
    (κ : ℝ) (hκ : 0 < κ) (hF : NecoaraNG.Chain.QuadFunGrowth X f κ)
    (β L Lbar : ℝ) (hβ : 0 < β) (hLpos : 0 < L) (hLbar : 0 < Lbar)
    (α : ℕ → ℝ) (e x : ℕ → NecoaraNG.Chain.E n) (hrun : IsFDMRun X f β L Lbar α e x) :
    ∀ k : ℕ, f (x k) - f xstar ≤
      (1 / (1 + L * κ / (4 * (Lf + Lbar + β * Lbar) ^ 2))) ^ k * (f (x 0) - f xstar) := by
  have hcont : ContinuousOn f X := fun y hy => (hdiff y hy).continuousAt.continuousWithinAt
  have hopt : NecoaraNG.Chain.optSet X f = X ∩ f ⁻¹' Set.Iic (f xstar) := by
    ext y
    constructor
    · intro h; exact ⟨h.1, h.2 xstar hxstar.1⟩
    · intro h; exact ⟨h.1, fun z hz => le_trans h.2 (hxstar.2 z hz)⟩
  have hoptc : IsClosed (NecoaraNG.Chain.optSet X f) := by
    rw [hopt]; exact hcont.preimage_isClosed_of_isClosed hXc isClosed_Iic
  have hoptv : Convex ℝ (NecoaraNG.Chain.optSet X f) := by
    rw [hopt]; exact hf.convex_le (f xstar)
  obtain ⟨hx0, hstep⟩ := hrun
  have hxX : ∀ k, x k ∈ X := by
    intro k
    cases k with
    | zero => exact hx0
    | succ k => exact (hstep k).1.1
  set C := Lf + Lbar + β * Lbar with hCdef
  have hC : 0 < C := by positivity
  have one : ∀ k, f (x (k + 1)) - f xstar ≤ 1 / (1 + L * κ / (4 * C ^ 2)) * (f (x k) - f xstar) := by
    intro k
    obtain ⟨hproj, he, hdesc, hα⟩ := hstep k
    obtain ⟨xb, hxb⟩ := exists_nearest ⟨xstar, hxstar⟩ hoptc hoptv (x (k + 1))
    have hxbX : xb ∈ X := hxb.1.1
    have hfxb : f xb = f xstar := le_antisymm (hxb.1.2 xstar hxstar.1) (hxstar.2 xb hxbX)
    have hαpos : 0 < α k := lt_of_lt_of_le (by positivity) hα
    have hαinv : 1 / α k ≤ Lbar := by
      rw [div_le_iff₀ hαpos]
      rw [div_le_iff₀ hLbar] at hα
      linarith
    set xp := x (k + 1) with hxp
    set xk := x k with hxk
    set Δ := xp - xk with hΔ
    set r := ‖xp - xb‖ with hr
    -- projection inequality
    have hvi := proj_vi hXconv hproj xb hxbX
    have e1 : xk - α k • gradient f xk + e k - xp = (e k - Δ) - α k • gradient f xk := by
      rw [hΔ]; abel
    rw [e1, inner_sub_left, inner_smul_left] at hvi
    simp only [RCLike.conj_to_real] at hvi
    have hcs : -⟪e k - Δ, xb - xp⟫_ℝ ≤ (1 + β) * ‖Δ‖ * r := by
      have h0 := abs_real_inner_le_norm (e k - Δ) (xb - xp)
      have h1 : -⟪e k - Δ, xb - xp⟫_ℝ ≤ ‖e k - Δ‖ * ‖xb - xp‖ := (neg_le_abs _).trans h0
      have h2 : ‖e k - Δ‖ ≤ ‖e k‖ + ‖Δ‖ := norm_sub_le _ _
      rw [norm_sub_rev xb xp] at h1
      have h3 : ‖e k - Δ‖ * r ≤ (‖e k‖ + ‖Δ‖) * r := mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
      have h4 : ‖e k‖ * r ≤ β * ‖Δ‖ * r := by
        rw [hΔ]; exact mul_le_mul_of_nonneg_right he (norm_nonneg _)
      nlinarith
    -- α ⟪g_k, xp - xb⟫ ≤ (1+β)‖Δ‖ r
    have hg1 : α k * ⟪gradient f xk, xp - xb⟫_ℝ ≤ (1 + β) * ‖Δ‖ * r := by
      have : ⟪gradient f xk, xp - xb⟫_ℝ = -⟪gradient f xk, xb - xp⟫_ℝ := by
        rw [← inner_neg_right, neg_sub]
      rw [this]; linarith
    have hg2 : ⟪gradient f xk, xp - xb⟫_ℝ ≤ Lbar * ((1 + β) * ‖Δ‖ * r) := by
      have hnn : 0 ≤ (1 + β) * ‖Δ‖ * r := by positivity
      have : ⟪gradient f xk, xp - xb⟫_ℝ ≤ (1 + β) * ‖Δ‖ * r / α k := by
        rw [le_div_iff₀ hαpos]; linarith
      calc _ ≤ (1 + β) * ‖Δ‖ * r / α k := this
        _ = 1 / α k * ((1 + β) * ‖Δ‖ * r) := by ring
        _ ≤ Lbar * ((1 + β) * ‖Δ‖ * r) := mul_le_mul_of_nonneg_right hαinv hnn
    -- convexity at xp
    have hfo := first_order hXconv f hf hdiff (hxX (k + 1)) hxbX
    have hlip := hL xp (hxX (k + 1)) xk (hxX k)
    have hg3 : ⟪gradient f xp - gradient f xk, xp - xb⟫_ℝ ≤ Lf * ‖Δ‖ * r := by
      have := real_inner_le_norm (gradient f xp - gradient f xk) (xp - xb)
      have h2 := mul_le_mul_of_nonneg_right hlip (norm_nonneg (xp - xb))
      rw [hΔ, hr]; linarith
    have hδ : f xp - f xstar ≤ C * ‖Δ‖ * r := by
      have e2 : ⟪gradient f xp, xb - xp⟫_ℝ = -⟪gradient f xp, xp - xb⟫_ℝ := by
        rw [← inner_neg_right, neg_sub]
      rw [e2] at hfo
      rw [inner_sub_left] at hg3
      rw [hCdef]
      nlinarith
    have hQ := hF xp (hxX (k + 1)) xb hxb
    rw [hfxb] at hQ
    have hδ0 : 0 ≤ f xp - f xstar := sub_nonneg.2 (hxstar.2 _ (hxX (k + 1)))
    exact num_step _ _ C L κ ‖Δ‖ r hC hLpos hκ hδ0 (norm_nonneg _) (norm_nonneg _) hδ hQ
      (by rw [hΔ]; linarith)
  have hρ : 0 ≤ 1 / (1 + L * κ / (4 * C ^ 2)) := by positivity
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    calc f (x (k + 1)) - f xstar ≤ 1 / (1 + L * κ / (4 * C ^ 2)) * (f (x k) - f xstar) := one k
      _ ≤ 1 / (1 + L * κ / (4 * C ^ 2)) *
          ((1 / (1 + L * κ / (4 * C ^ 2))) ^ k * (f (x 0) - f xstar)) :=
          mul_le_mul_of_nonneg_left ih hρ
      _ = _ := by ring

#print axioms solution
