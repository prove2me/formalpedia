-- Prove2me | solution 1 for NecoaraNG.ErrBound.theorem_7
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-09T18:45:40.182992+00:00
-- url     : https://prove2.me/submissions/1951634f-a16c-495c-b0ed-73ee1f571078

import Mathlib
import Definitions.Def_NecoaraNG_ErrBound_Setting

open scoped InnerProductSpace

namespace RRAux_NecoaraNG_ErrBound_theorem_7

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

theorem descent {S : Set F} (hS : Convex ℝ S) {φ : F → ℝ}
    (hd : ∀ z ∈ S, DifferentiableAt ℝ φ z) {L : ℝ}
    (hL : ∀ u ∈ S, ∀ w ∈ S, ‖gradient φ u - gradient φ w‖ ≤ L * ‖u - w‖) {x y : F}
    (hx : x ∈ S) (hy : y ∈ S) :
    φ y ≤ φ x + ⟪gradient φ x, y - x⟫_ℝ + L / 2 * ‖y - x‖ ^ 2 := by
  set v := y - x with hv
  let h : ℝ → ℝ := fun s => φ (x + s • v) - s * ⟪gradient φ x, v⟫_ℝ - L / 2 * s ^ 2 * ‖v‖ ^ 2
  have hmem : ∀ s ∈ Set.Icc (0:ℝ) 1, x + s • v ∈ S := fun s hs => hS.add_smul_sub_mem hx hy hs
  have hder : ∀ s ∈ Set.Icc (0:ℝ) 1, HasDerivAt h
      (⟪gradient φ (x + s • v), v⟫_ℝ - ⟪gradient φ x, v⟫_ℝ - L * s * ‖v‖ ^ 2) s := by
    intro s hs
    have h1 := line_hasDerivAt (hd _ (hmem s hs))
    have h2 := (hasDerivAt_id s).mul_const ⟪gradient φ x, v⟫_ℝ
    have h3 := ((hasDerivAt_pow 2 s).const_mul (L / 2)).mul_const (‖v‖ ^ 2)
    have h4 := (h1.sub h2).sub h3
    have e : ⟪gradient φ (x + s • v), v⟫_ℝ - 1 * ⟪gradient φ x, v⟫_ℝ
        - L / 2 * ((2:ℕ) * s ^ (2 - 1)) * ‖v‖ ^ 2
        = ⟪gradient φ (x + s • v), v⟫_ℝ - ⟪gradient φ x, v⟫_ℝ - L * s * ‖v‖ ^ 2 := by
      push_cast; ring
    rw [e] at h4
    exact h4
  have hanti : AntitoneOn h (Set.Icc 0 1) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 1)
    · intro s hs; exact (hder s hs).continuousAt.continuousWithinAt
    · intro s hs
      exact (hder s (interior_subset hs)).hasDerivWithinAt
    · intro s hs
      have hs' := interior_subset hs
      have hs0 : 0 ≤ s := hs'.1
      have hc := real_inner_le_norm (gradient φ (x + s • v) - gradient φ x) v
      have hl := hL _ (hmem s hs') x hx
      have hn : ‖x + s • v - x‖ = s * ‖v‖ := by
        simp [norm_smul, abs_of_nonneg hs0]
      rw [hn] at hl
      rw [← inner_sub_left]
      have hv0 : 0 ≤ ‖v‖ := norm_nonneg _
      nlinarith [mul_le_mul_of_nonneg_right hl hv0]
  have := hanti (by simp : (0:ℝ) ∈ Set.Icc (0:ℝ) 1) (by simp : (1:ℝ) ∈ Set.Icc (0:ℝ) 1)
    zero_le_one
  simp only [h, one_smul, zero_smul, add_zero, zero_mul, one_mul, one_pow, sub_zero,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] at this
  have hxy : x + v = y := by rw [hv]; abel
  rw [hxy] at this
  linarith

omit [CompleteSpace F] in
theorem proj_vi {K : Set F} (hK : Convex ℝ K) {u p : F} (hp : p ∈ K)
    (hmin : ∀ z ∈ K, ‖u - p‖ ≤ ‖u - z‖) : ∀ z ∈ K, ⟪u - p, z - p⟫_ℝ ≤ 0 := by
  apply (norm_eq_iInf_iff_real_inner_le_zero hK hp).mp
  have : Nonempty K := ⟨⟨p, hp⟩⟩
  apply le_antisymm
  · exact le_ciInf fun w => hmin w w.2
  · exact ciInf_le ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩ (⟨p, hp⟩ : K)

theorem quad_root (κ L D r s : ℝ) (hκ : 0 < κ) (hL : 0 < L) (hD : 0 ≤ D) (hr : 0 ≤ r)
    (hs : 0 ≤ s) (hs2 : L * s ^ 2 = L + κ)
    (h : κ / 2 * r ^ 2 ≤ L * D * r + L * D ^ 2 / 2) : κ * r ≤ L * D * (1 + s) := by
  by_contra hc
  have hc := not_le.mp hc
  have h1 : L * D * s < κ * r - L * D := by linarith
  have h0 : 0 ≤ L * D * s := by positivity
  have h2 : (L * D * s) ^ 2 < (κ * r - L * D) ^ 2 := by
    have := mul_self_lt_mul_self h0 h1
    nlinarith
  have h3 : (L * D * s) ^ 2 = L * D ^ 2 * (L * s ^ 2) := by ring
  rw [h3, hs2] at h2
  nlinarith [mul_le_mul_of_nonneg_left h hκ.le]

end RRAux_NecoaraNG_ErrBound_theorem_7

open RRAux_NecoaraNG_ErrBound_theorem_7 in
open NecoaraNG.ErrBound in
theorem solution {n : ℕ} (X : Set (NecoaraNG.Chain.E n)) (hXc : IsClosed X) (hXconv : Convex ℝ X)
    (f : NecoaraNG.Chain.E n → ℝ) (hf : ConvexOn ℝ X f) (hdiff : ∀ x ∈ X, DifferentiableAt ℝ f x)
    (Lf : ℝ) (hLf : 0 < Lf)
    (hL : ∀ x ∈ X, ∀ y ∈ X, ‖gradient f x - gradient f y‖ ≤ Lf * ‖x - y‖)
    (xstar : NecoaraNG.Chain.E n) (hxstar : xstar ∈ NecoaraNG.Chain.optSet X f)
    (κ : ℝ) (hκ : 0 < κ) (hF : NecoaraNG.Chain.QuadFunGrowth X f κ) :
    ErrorBound X f Lf (κ / (1 + κ / Lf + Real.sqrt (1 + κ / Lf))) := by
  intro x hx xbar hxbar xp hxp
  obtain ⟨hxpX, hxpmin⟩ := hxp
  -- the optimal set is closed and nonempty
  have hcont : ContinuousOn f X := fun z hz => (hdiff z hz).continuousAt.continuousWithinAt
  have hopt : NecoaraNG.Chain.optSet X f = X ∩ f ⁻¹' Set.Iic (f xstar) := by
    ext z
    simp only [NecoaraNG.Chain.optSet, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_Iic]
    constructor
    · rintro ⟨hz, hmin⟩; exact ⟨hz, hmin _ hxstar.1⟩
    · rintro ⟨hz, hle⟩; exact ⟨hz, fun y hy => hle.trans (hxstar.2 y hy)⟩
  have hclosed : IsClosed (NecoaraNG.Chain.optSet X f) := by
    rw [hopt]; exact hcont.preimage_isClosed_of_isClosed hXc isClosed_Iic
  obtain ⟨z, hz, hzd⟩ := hclosed.exists_infDist_eq_dist ⟨xstar, hxstar⟩ xp
  have hznear : NecoaraNG.Chain.IsNearest (NecoaraNG.Chain.optSet X f) xp z := by
    refine ⟨hz, fun w hw => ?_⟩
    rw [← dist_eq_norm, ← dist_eq_norm, ← hzd]
    exact Metric.infDist_le_dist_of_mem hw
  have hzX : z ∈ X := hz.1
  -- the three inequalities
  have hdesc := descent hXconv hdiff hL hx hxpX
  have hconv := convex_first_order hf hx hzX (hdiff x hx)
  have hvi := proj_vi hXconv hxpX hxpmin z hzX
  have hqfg := hF xp hxpX z hznear
  set g := gradient f x
  set d := x - xp with hd
  set D := ‖d‖ with hDdef
  set r := ‖xp - z‖ with hr
  -- rewrite the VI
  have e1 : x - (1 / Lf) • g - xp = d - (1 / Lf) • g := by rw [hd]; abel
  rw [e1, inner_sub_left, real_inner_smul_left] at hvi
  have e2 : z - xp = (z - x) + d := by rw [hd]; abel
  have e3 : xp - x = -d := by rw [hd]; abel
  rw [e3, inner_neg_right, norm_neg] at hdesc
  have hgz : ⟪g, z - xp⟫_ℝ = ⟪g, z - x⟫_ℝ + ⟪g, d⟫_ℝ := by rw [e2, inner_add_right]
  have hdz : ⟪d, z - xp⟫_ℝ = ⟪d, z - x⟫_ℝ + D ^ 2 := by
    rw [e2, inner_add_right, real_inner_self_eq_norm_sq]
  -- L ⟪d, z - xp⟫ ≤ ⟪g, z - xp⟫
  have hvi2 : Lf * ⟪d, z - xp⟫_ℝ ≤ ⟪g, z - xp⟫_ℝ := by
    have := mul_le_mul_of_nonneg_left hvi hLf.le
    have e : Lf * (1 / Lf * ⟪g, z - xp⟫_ℝ) = ⟪g, z - xp⟫_ℝ := by field_simp
    linarith
  -- f z ≥ f xp + L ⟪d, z - x⟫ + L/2 D²
  have hfz : f xp + Lf * ⟪d, z - x⟫_ℝ + Lf / 2 * D ^ 2 ≤ f z := by
    rw [hdz] at hvi2
    rw [hgz] at hvi2
    nlinarith
  -- Cauchy–Schwarz and triangle
  have hcs : -⟪d, z - x⟫_ℝ ≤ D * ‖z - x‖ := by
    have := real_inner_le_norm d (x - z)
    rw [norm_sub_rev x z] at this
    rw [← inner_neg_right, neg_sub]; exact this
  have htri : ‖z - x‖ ≤ r + D := by
    have : z - x = -(xp - z) - d := by rw [hd]; abel
    rw [this]
    calc ‖-(xp - z) - d‖ ≤ ‖-(xp - z)‖ + ‖d‖ := norm_sub_le _ _
      _ = r + D := by rw [norm_neg]
  have hD0 : 0 ≤ D := norm_nonneg _
  have hr0 : 0 ≤ r := norm_nonneg _
  have hquad : κ / 2 * r ^ 2 ≤ Lf * D * r + Lf * D ^ 2 / 2 := by
    have h1 : Lf * (-⟪d, z - x⟫_ℝ) ≤ Lf * (D * (r + D)) :=
      mul_le_mul_of_nonneg_left (hcs.trans (mul_le_mul_of_nonneg_left htri hD0)) hLf.le
    have h2 : κ / 2 * ‖xp - z‖ ^ 2 ≤ f xp - f z := hqfg
    nlinarith
  set s := Real.sqrt (1 + κ / Lf) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : Lf * s ^ 2 = Lf + κ := by
    rw [hs, Real.sq_sqrt (by positivity)]; field_simp
  have hroot := quad_root κ Lf D r s hκ hLf hD0 hr0 hs0 hs2 hquad
  have hnear : ‖x - xbar‖ ≤ ‖x - z‖ := hxbar.2 z hz
  have hxz : ‖x - z‖ ≤ r + D := by rw [norm_sub_rev]; exact htri
  have hG : ‖Lf • (x - xp)‖ = Lf * D := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hLf]
  rw [hG, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  have e4 : Lf * D * (1 + κ / Lf + s) = κ * D + Lf * D * (1 + s) := by
    field_simp; ring
  rw [e4]
  nlinarith [mul_le_mul_of_nonneg_left (hnear.trans hxz) hκ.le]

#print axioms solution
