-- Prove2me | solution 1 for NecoaraNG.Compose.theorem_8
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-09T18:51:10.151754+00:00
-- url     : https://prove2.me/submissions/1eb8a36d-9033-4d48-b1c5-e036ef3eb490

import Mathlib
import Definitions.Def_NecoaraNG_Compose_Setting

open scoped InnerProductSpace

namespace RRAux_NecoaraNG_Compose_theorem_8

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

theorem sc_first_order {g : F → ℝ} {σ : ℝ} (hg : StrongConvexOn Set.univ σ g)
    (hdiff : ∀ u, DifferentiableAt ℝ g u) (x z : F) :
    g x + ⟪gradient g x, z - x⟫_ℝ + σ / 2 * ‖z - x‖ ^ 2 ≤ g z := by
  have hc := (strongConvexOn_iff_convex.mp hg)
  set v := z - x with hv
  have hl : HasDerivAt (fun s : ℝ => x + s • v) v 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add x
  have h1 := line_hasDerivAt (φ := g) (x := x) (v := v) (t := 0) (hdiff _)
  simp only [zero_smul, add_zero] at h1
  have h2 := (hl.norm_sq).const_mul (σ / 2)
  simp only [zero_smul, add_zero] at h2
  have h3 := h1.sub h2
  have := convex_first_order_line (φ := fun x => g x - σ / 2 * ‖x‖ ^ 2) hc
    (Set.mem_univ x) (Set.mem_univ z) (D := ⟪gradient g x, v⟫_ℝ - σ / 2 * (2 * ⟪x, v⟫_ℝ)) h3
  have hz : z = x + v := by rw [hv]; abel
  have hn := norm_add_sq_real x v
  rw [← hz] at hn
  have hm : σ / 2 * ‖z‖ ^ 2 = σ / 2 * ‖x‖ ^ 2 + σ * ⟪x, v⟫_ℝ + σ / 2 * ‖v‖ ^ 2 := by
    rw [hn]; ring
  linarith

theorem grad_comp {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
    (A : G →L[ℝ] F) {g : F → ℝ} (hgd : ∀ u, DifferentiableAt ℝ g u) (x : G) :
    gradient (fun x => g (A x)) x = ContinuousLinearMap.adjoint A (gradient g (A x)) := by
  apply HasGradientAt.gradient
  rw [hasGradientAt_iff_hasFDerivAt]
  have h := (hgd (A x)).hasGradientAt.hasFDerivAt.comp x A.hasFDerivAt
  have heq : InnerProductSpace.toDual ℝ G (ContinuousLinearMap.adjoint A (gradient g (A x)))
      = (InnerProductSpace.toDual ℝ F (gradient g (A x))).comp A := by
    ext v
    simp only [InnerProductSpace.toDual_apply_apply, ContinuousLinearMap.coe_comp',
      Function.comp_apply, ContinuousLinearMap.adjoint_inner_left]
  rw [heq]; exact h

end RRAux_NecoaraNG_Compose_theorem_8

open RRAux_NecoaraNG_Compose_theorem_8 in
open NecoaraNG.Compose in
theorem solution {n m p : ℕ} (A : NecoaraNG.Chain.E n →L[ℝ] NecoaraNG.Chain.E m) (hA : A ≠ 0) (C : NecoaraNG.Chain.E n →L[ℝ] NecoaraNG.Chain.E p)
    (d : NecoaraNG.Chain.E p) (g : NecoaraNG.Chain.E m → ℝ) (hgdiff : ∀ u, DifferentiableAt ℝ g u) (σg Lg : ℝ) (hσg : 0 < σg)
    (hg : StrongConvexOn Set.univ σg g)
    (hLg : ∀ u v, ‖gradient g u - gradient g v‖ ≤ Lg * ‖u - v‖)
    (xstar : NecoaraNG.Chain.E n) (hxstar : xstar ∈ NecoaraNG.Chain.optSet (polyhedron C d) (fun x => g (A x)))
    (θ : ℝ) (hθ : 0 < θ) (hHoff : IsHoffmanConst A C (A xstar) d θ) :
    ConvexOn ℝ (polyhedron C d) (fun x => g (A x)) ∧
      LipGradOn (polyhedron C d) (fun x => g (A x)) (Lg * ‖A‖ ^ 2) ∧
      NecoaraNG.Chain.QuasiStrong (polyhedron C d) (fun x => g (A x)) (σg / θ ^ 2) := by
  have hXconv : Convex ℝ (polyhedron C d) := by
    intro x hx y hy a b ha hb hab i
    have e : C (a • x + b • y) i = a * C x i + b * C y i := by simp
    rw [e]
    have h1 := mul_le_mul_of_nonneg_left (hx i) ha
    have h2 := mul_le_mul_of_nonneg_left (hy i) hb
    have h3 : a * d i + b * d i = d i := by rw [← add_mul, hab, one_mul]
    linarith
  have hgconv : ConvexOn ℝ Set.univ g := hg.convexOn (fun r => by positivity)
  refine ⟨?_, ?_, ?_⟩
  · -- convexity
    have := hgconv.comp_linearMap (A : NecoaraNG.Chain.E n →ₗ[ℝ] NecoaraNG.Chain.E m)
    exact (this.subset (Set.subset_univ _) hXconv)
  · -- Lipschitz gradient
    have hLg0 : 0 ≤ Lg := by
      obtain ⟨x, hx⟩ : ∃ x, A x ≠ 0 := by
        by_contra h
        exact hA (ContinuousLinearMap.ext fun x => by
          by_contra hx; exact h ⟨x, by simpa using hx⟩)
      have h1 := hLg (A x) 0
      rw [sub_zero] at h1
      have h2 : 0 < ‖A x‖ := norm_pos_iff.mpr hx
      by_contra hneg
      have : Lg * ‖A x‖ < 0 := mul_neg_of_neg_of_pos (lt_of_not_ge hneg) h2
      linarith [norm_nonneg (gradient g (A x) - gradient g 0)]
    intro x _ y _
    rw [grad_comp A hgdiff, grad_comp A hgdiff, ← map_sub]
    have hadj : ‖ContinuousLinearMap.adjoint A‖ = ‖A‖ := LinearIsometryEquiv.norm_map _ _
    have h1 := (ContinuousLinearMap.adjoint A).le_opNorm (gradient g (A x) - gradient g (A y))
    rw [hadj] at h1
    have h2 := hLg (A x) (A y)
    have h3 : ‖A x - A y‖ ≤ ‖A‖ * ‖x - y‖ := by rw [← map_sub]; exact A.le_opNorm _
    have hA0 : 0 ≤ ‖A‖ := norm_nonneg _
    calc _ ≤ ‖A‖ * ‖gradient g (A x) - gradient g (A y)‖ := h1
      _ ≤ ‖A‖ * (Lg * (‖A‖ * ‖x - y‖)) := by
          apply mul_le_mul_of_nonneg_left _ hA0
          exact h2.trans (mul_le_mul_of_nonneg_left h3 hLg0)
      _ = Lg * ‖A‖ ^ 2 * ‖x - y‖ := by ring
  · -- quasi-strong convexity
    -- the optimal set is the polyhedron's slice A z = A xstar
    have hopt : ∀ z, z ∈ NecoaraNG.Chain.optSet (polyhedron C d) (fun x => g (A x)) →
        A z = A xstar := by
      intro z hz
      by_contra hne
      have hzX := hz.1
      have hle1 := hz.2 xstar hxstar.1
      have hle2 := hxstar.2 z hzX
      simp only at hle1 hle2
      set mid := (1 / 2 : ℝ) • z + (1 / 2 : ℝ) • xstar
      have hmid : mid ∈ polyhedron C d :=
        hXconv hzX hxstar.1 (by norm_num) (by norm_num) (by norm_num)
      have hsc := hg.2 (Set.mem_univ (A z)) (Set.mem_univ (A xstar))
        (by norm_num : (0:ℝ) ≤ 1 / 2) (by norm_num : (0:ℝ) ≤ 1 / 2) (by norm_num)
      have hAmid : A mid = (1 / 2 : ℝ) • A z + (1 / 2 : ℝ) • A xstar := by
        simp [mid, map_add, map_smul]
      have hpos : 0 < ‖A z - A xstar‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
      have hopt2 := hxstar.2 mid hmid
      simp only at hopt2
      rw [hAmid] at hopt2
      simp only [smul_eq_mul] at hsc
      nlinarith [sq_pos_of_pos hpos]
    intro x hx xbar hxbar
    have hxbarA : A xbar = A xstar := hopt xbar hxbar.1
    have hnear' : NecoaraNG.Chain.IsNearest
        {z | A z = A xstar ∧ ∀ i, C z i ≤ d i} x xbar := by
      refine ⟨⟨hxbarA, hxbar.1.1⟩, fun z hz => hxbar.2 z ⟨hz.2, fun y hy => ?_⟩⟩
      have := hxstar.2 y hy
      simp only at this ⊢
      rw [hz.1]; exact this
    have hH := hHoff x xbar hnear'
    have hpp : posPart (C x - d) = 0 := by
      ext i
      have hi : C x i ≤ d i := hx i
      simp [NecoaraNG.Compose.posPart, hi]
    rw [hpp, norm_zero, ← hxbarA] at hH
    rw [show (0:ℝ) ^ 2 = 0 by norm_num, add_zero, Real.sqrt_sq (norm_nonneg _), ← map_sub] at hH
    have hsc := sc_first_order hg hgdiff (A x) (A xbar)
    rw [← map_sub, ← ContinuousLinearMap.adjoint_inner_left, ← grad_comp A hgdiff] at hsc
    simp only
    have hsq : ‖x - xbar‖ ^ 2 ≤ θ ^ 2 * ‖A (xbar - x)‖ ^ 2 := by
      have e : ‖A (x - xbar)‖ = ‖A (xbar - x)‖ := by rw [← norm_neg, ← map_neg, neg_sub]
      rw [e] at hH
      have := pow_le_pow_left₀ (norm_nonneg _) hH 2
      rw [mul_pow] at this
      exact this
    have hθ2 : 0 < θ ^ 2 := by positivity
    have : σg / θ ^ 2 / 2 * ‖x - xbar‖ ^ 2 ≤ σg / 2 * ‖A (xbar - x)‖ ^ 2 := by
      rw [div_div, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith
    linarith

#print axioms solution
