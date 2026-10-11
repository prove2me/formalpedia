-- Prove2me | solution 1 for NecoaraNG.GMIff.theorem_13
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T22:14:50.118009+00:00
-- url     : https://prove2.me/submissions/a36ca86f-cf77-4ca5-9062-16e11a0ca8a2

import Mathlib
import Definitions.Def_NecoaraNG_GMIff_Setting

namespace RRAux_NecoaraNG_GMIff_theorem_13

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

theorem descentX {X : Set F} (hXconv : Convex ℝ X) (f : F → ℝ)
    (hdiff : ∀ x ∈ X, DifferentiableAt ℝ f x) (L : ℝ)
    (hL : ∀ x ∈ X, ∀ y ∈ X, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    {x y : F} (hx : x ∈ X) (hy : y ∈ X) :
    f y ≤ f x + ⟪gradient f x, y - x⟫_ℝ + L / 2 * ‖y - x‖ ^ 2 := by
  set w := y - x with hw
  have hmem : ∀ t ∈ Set.Icc (0:ℝ) 1, x + t • w ∈ X := fun t ht =>
    hXconv.add_smul_sub_mem hx hy ht
  set ψ : ℝ → ℝ := fun t => f (x + t • w) - t * ⟪gradient f x, w⟫_ℝ - L / 2 * t ^ 2 * ‖w‖ ^ 2
    with hψ
  have hder : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt ψ (⟪gradient f (x + t • w), w⟫_ℝ
      - ⟪gradient f x, w⟫_ℝ - L / 2 * (2 * t) * ‖w‖ ^ 2) t := by
    intro t ht
    have hc := line_deriv f x w t (hdiff _ (hmem t ht))
    have h2 : HasDerivAt (fun t : ℝ => t * ⟪gradient f x, w⟫_ℝ) ⟪gradient f x, w⟫_ℝ t := by
      simpa using (hasDerivAt_id t).mul_const ⟪gradient f x, w⟫_ℝ
    have h3 : HasDerivAt (fun t : ℝ => L / 2 * t ^ 2 * ‖w‖ ^ 2) (L / 2 * (2 * t) * ‖w‖ ^ 2) t := by
      have := ((hasDerivAt_pow 2 t).const_mul (L / 2)).mul_const (‖w‖ ^ 2)
      simpa using this
    exact (hc.sub h2).sub h3
  have hanti : AntitoneOn ψ (Set.Icc 0 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
    · intro t ht; exact (hder t ht).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      exact (hder t (Set.Ioo_subset_Icc_self ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      have ht' := Set.Ioo_subset_Icc_self ht
      rw [(hder t ht').deriv]
      have h1 := real_inner_le_norm (gradient f (x + t • w) - gradient f x) w
      have h2 := hL _ (hmem t ht') x hx
      have e : x + t • w - x = t • w := by abel
      rw [e, norm_smul, Real.norm_eq_abs, abs_of_pos ht.1] at h2
      rw [inner_sub_left] at h1
      have h3 := mul_le_mul_of_nonneg_right h2 (norm_nonneg w)
      nlinarith
  have := hanti (show (0:ℝ) ∈ Set.Icc 0 1 by simp) (show (1:ℝ) ∈ Set.Icc 0 1 by simp) zero_le_one
  simp only [hψ, zero_smul, add_zero, one_smul, zero_mul, sub_zero, one_mul] at this
  have e : x + w = y := by rw [hw]; abel
  rw [e] at this
  norm_num at this
  rw [grad_inner f] at this
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

open NecoaraNG.Chain in
theorem three_point {n : ℕ} {X : Set (E n)} (hXconv : Convex ℝ X) (f : E n → ℝ)
    (hf : ConvexOn ℝ X f) (hdiff : ∀ x ∈ X, DifferentiableAt ℝ f x) (L : ℝ) (hLp : 0 < L)
    (hL : ∀ x ∈ X, ∀ y ∈ X, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    {x z xp : E n} (hx : x ∈ X) (hz : z ∈ X) (hp : NecoaraNG.ErrBound.IsPGStep X f L x xp) :
    f xp ≤ f z + L / 2 * (‖x - z‖ ^ 2 - ‖xp - z‖ ^ 2) := by
  have hpX : xp ∈ X := hp.1
  have hd := descentX hXconv f hdiff L hL hx hpX
  have hc := first_order hXconv f hf hdiff hx hz
  have hvi := proj_vi hXconv hp z hz
  set g := gradient f x with hg
  set a := x - xp with ha
  set b := z - xp with hb
  have e1 : x - (1 / L) • g - xp = a - (1 / L) • g := by rw [ha]; abel
  have e2 : z - x = b - a := by rw [ha, hb]; abel
  have e3 : xp - x = -a := by rw [ha]; abel
  have e4 : x - z = a - b := by rw [ha, hb]; abel
  have e5 : xp - z = -b := by rw [hb]; abel
  rw [e1, inner_sub_left, inner_smul_left] at hvi
  rw [e2, inner_sub_right] at hc
  rw [e3, inner_neg_right, norm_neg] at hd
  rw [e4, e5, norm_neg, norm_sub_sq_real]
  simp only [RCLike.conj_to_real] at hvi
  have hm : L * ⟪a, b⟫_ℝ ≤ ⟪g, b⟫_ℝ := by
    have := mul_le_mul_of_nonneg_left hvi hLp.le
    rw [mul_sub, ← mul_assoc, mul_one_div_cancel hLp.ne', one_mul, mul_zero] at this
    linarith
  nlinarith

end RRAux_NecoaraNG_GMIff_theorem_13

open scoped InnerProductSpace
open RRAux_NecoaraNG_GMIff_theorem_13

open NecoaraNG.GMIff in
theorem solution (n : ℕ) (X : Set (NecoaraNG.Chain.E n)) (hXc : IsClosed X) (hXconv : Convex ℝ X)
    (f : NecoaraNG.Chain.E n → ℝ) (hf : ConvexOn ℝ X f)
    (hdiff : ∀ x ∈ X, DifferentiableAt ℝ f x)
    (Lf : ℝ) (hLf : 0 < Lf)
    (hL : ∀ x ∈ X, ∀ y ∈ X, ‖gradient f x - gradient f y‖ ≤ Lf * ‖x - y‖)
    (xstar : NecoaraNG.Chain.E n) (hxstar : xstar ∈ NecoaraNG.Chain.optSet X f) :
    (∀ κ : ℝ, 0 < κ → NecoaraNG.Chain.QuadFunGrowth X f κ →
      ∀ x ∈ X, ∀ xbar, NecoaraNG.Chain.IsNearest (NecoaraNG.Chain.optSet X f) x xbar → ∀ xp, NecoaraNG.ErrBound.IsPGStep X f Lf x xp →
        ∀ xpbar, NecoaraNG.Chain.IsNearest (NecoaraNG.Chain.optSet X f) xp xpbar →
          ‖xp - xpbar‖ ^ 2 ≤ 1 / (1 + κ / Lf) * ‖x - xbar‖ ^ 2)
    ∧
    (∀ β : ℝ, 0 < β → β < 1 →
      (∀ x ∈ X, ∀ xbar, NecoaraNG.Chain.IsNearest (NecoaraNG.Chain.optSet X f) x xbar → ∀ xp, NecoaraNG.ErrBound.IsPGStep X f Lf x xp →
        ∀ xpbar, NecoaraNG.Chain.IsNearest (NecoaraNG.Chain.optSet X f) xp xpbar → ‖xp - xpbar‖ ≤ β * ‖x - xbar‖) →
      NecoaraNG.Chain.QuadFunGrowth X f (Lf * (1 - β) ^ 2)) := by
  constructor
  · intro κ hκ hQ x hx xbar hxbar xp hxp xpbar hxpbar
    have hxbarX : xbar ∈ X := hxbar.1.1
    have tp := three_point hXconv f hf hdiff Lf hLf hL hx hxbarX hxp
    have hq := hQ xp hxp.1 xpbar hxpbar
    have h1 : f xbar ≤ f xpbar := hxbar.1.2 xpbar hxpbar.1.1
    have h2 : f xpbar ≤ f xbar := hxpbar.1.2 xbar hxbarX
    have h3 : ‖xp - xpbar‖ ≤ ‖xp - xbar‖ := hxpbar.2 xbar hxbar.1
    have h4 : ‖xp - xpbar‖ ^ 2 ≤ ‖xp - xbar‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h3 2
    have h5 : (κ + Lf) * ‖xp - xpbar‖ ^ 2 ≤ Lf * ‖x - xbar‖ ^ 2 := by nlinarith
    have e : 1 / (1 + κ / Lf) * ‖x - xbar‖ ^ 2 = Lf * ‖x - xbar‖ ^ 2 / (κ + Lf) := by
      field_simp; ring
    rw [e, le_div_iff₀ (by linarith)]
    linarith
  · intro β hβ0 hβ1 H x hx xbar hxbar
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
    obtain ⟨xp, hxp⟩ := exists_nearest ⟨x, hx⟩ hXc hXconv (x - (1 / Lf) • gradient f x)
    obtain ⟨xpbar, hxpbar⟩ := exists_nearest ⟨xstar, hxstar⟩ hoptc hoptv xp
    have hH := H x hx xbar hxbar xp hxp xpbar hxpbar
    have h1 : ‖x - xbar‖ ≤ ‖x - xpbar‖ := hxbar.2 xpbar hxpbar.1
    have h2 : ‖x - xpbar‖ ≤ ‖x - xp‖ + ‖xp - xpbar‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    have h3 : (1 - β) * ‖x - xbar‖ ≤ ‖x - xp‖ := by linarith
    have h4 : ((1 - β) * ‖x - xbar‖) ^ 2 ≤ ‖x - xp‖ ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg (by linarith) (norm_nonneg _)) h3 2
    have sd := three_point hXconv f hf hdiff Lf hLf hL hx hx hxp
    rw [sub_self, norm_zero, norm_sub_rev] at sd
    have h5 : f xbar ≤ f xp := hxbar.1.2 xp hxp.1
    have h6 : Lf * ((1 - β) * ‖x - xbar‖) ^ 2 ≤ Lf * ‖x - xp‖ ^ 2 :=
      mul_le_mul_of_nonneg_left h4 hLf.le
    have e : Lf * (1 - β) ^ 2 / 2 * ‖x - xbar‖ ^ 2 = Lf * ((1 - β) * ‖x - xbar‖) ^ 2 / 2 := by ring
    rw [e]
    linarith

#print axioms solution
