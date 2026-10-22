-- Prove2me | solution 1 for NecoaraNG.ErrBound.gradient_mapping_29
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:36:02.978913+00:00
-- url     : https://prove2.me/submissions/7c1d34e7-f2fc-4fb7-9189-ba84bdc6b844

import Mathlib
import Definitions.Def_NecoaraNG_Chain_Setting
import Definitions.Def_NecoaraNG_ErrBound_Setting
set_option autoImplicit false
open scoped InnerProductSpace

namespace ZZC

variable {n : ℕ}

/-- derivative of `f` along a segment inside the domain of differentiability. -/
lemma line_deriv (f : NecoaraNG.Chain.E n → ℝ) (X : Set (NecoaraNG.Chain.E n))
    (hdiff : ∀ x ∈ X, DifferentiableAt ℝ f x) (x d : NecoaraNG.Chain.E n) (t : ℝ)
    (ht : x + t • d ∈ X) :
    HasDerivAt (fun s : ℝ => f (x + s • d)) (⟪gradient f (x + t • d), d⟫_ℝ) t := by
  have h1 : HasFDerivAt f (fderiv ℝ f (x + t • d)) (x + t • d) := (hdiff _ ht).hasFDerivAt
  have hg : ⟪gradient f (x + t • d), d⟫_ℝ = fderiv ℝ f (x + t • d) d := by
    simp [gradient, InnerProductSpace.toDual_symm_apply]
  have h2 : HasDerivAt (fun s : ℝ => x + s • d) d t := by
    simpa using ((hasDerivAt_id t).smul_const d).const_add x
  have := h1.comp_hasDerivAt t h2
  rw [hg]
  exact this

lemma descent (f : NecoaraNG.Chain.E n → ℝ) (X : Set (NecoaraNG.Chain.E n)) (hXconv : Convex ℝ X)
    (hdiff : ∀ x ∈ X, DifferentiableAt ℝ f x) (Lf : ℝ) (hLf : 0 < Lf)
    (hL : ∀ x ∈ X, ∀ y ∈ X, ‖gradient f x - gradient f y‖ ≤ Lf * ‖x - y‖)
    (x y : NecoaraNG.Chain.E n) (hx : x ∈ X) (hy : y ∈ X) :
    f y ≤ f x + ⟪gradient f x, y - x⟫_ℝ + Lf / 2 * ‖y - x‖ ^ 2 := by
  set d := y - x with hd
  have hmem : ∀ t ∈ Set.Icc (0:ℝ) 1, x + t • d ∈ X := by
    intro t ht
    have := hXconv hx hy (by linarith [ht.2] : 0 ≤ 1 - t) ht.1 (by ring)
    convert this using 1
    simp only [hd, smul_sub]
    module
  set ψ : ℝ → ℝ := fun t => f (x + t • d) - t * ⟪gradient f x, d⟫_ℝ - Lf / 2 * t ^ 2 * ‖d‖ ^ 2 with hψ
  have hψd : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt ψ
      (⟪gradient f (x + t • d), d⟫_ℝ - ⟪gradient f x, d⟫_ℝ - Lf * t * ‖d‖ ^ 2) t := by
    intro t ht
    have h1 := line_deriv f X hdiff x d t (hmem t ht)
    have h2 : HasDerivAt (fun s : ℝ => s * ⟪gradient f x, d⟫_ℝ) (⟪gradient f x, d⟫_ℝ) t := by
      simpa using (hasDerivAt_id t).mul_const (⟪gradient f x, d⟫_ℝ)
    have h3 : HasDerivAt (fun s : ℝ => Lf / 2 * s ^ 2 * ‖d‖ ^ 2) (Lf * t * ‖d‖ ^ 2) t := by
      have := ((hasDerivAt_pow 2 t).const_mul (Lf / 2)).mul_const (‖d‖ ^ 2)
      exact this.congr_deriv (by first | ring | (norm_num; ring) | norm_num)
    exact (h1.sub h2).sub h3
  have hanti : AntitoneOn ψ (Set.Icc (0:ℝ) 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
    · exact fun t ht => (hψd t ht).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      exact (hψd t ⟨ht.1.le, ht.2.le⟩).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      have ht' : t ∈ Set.Icc (0:ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
      rw [(hψd t ht').deriv]
      have hpt := hmem t ht'
      have hlip := hL _ hpt x hx
      have hnorm : ‖x + t • d - x‖ = t * ‖d‖ := by
        rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht.1]
      rw [hnorm] at hlip
      have hcs := real_inner_le_norm (gradient f (x + t • d) - gradient f x) d
      have e1 : ⟪gradient f (x + t • d), d⟫_ℝ - ⟪gradient f x, d⟫_ℝ
          = ⟪gradient f (x + t • d) - gradient f x, d⟫_ℝ := by rw [inner_sub_left]
      rw [e1]
      have : ‖gradient f (x + t • d) - gradient f x‖ * ‖d‖ ≤ Lf * (t * ‖d‖) * ‖d‖ :=
        mul_le_mul_of_nonneg_right hlip (norm_nonneg _)
      nlinarith
  have h01 := hanti ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ zero_le_one
  simp only [hψ, zero_smul, add_zero, one_smul, zero_mul, mul_zero, sub_zero, one_mul] at h01
  have : x + d = y := by simp [hd]
  rw [this] at h01
  nlinarith

lemma gradineq (f : NecoaraNG.Chain.E n → ℝ) (X : Set (NecoaraNG.Chain.E n)) (hXconv : Convex ℝ X)
    (hf : ConvexOn ℝ X f) (hdiff : ∀ x ∈ X, DifferentiableAt ℝ f x)
    (x y : NecoaraNG.Chain.E n) (hx : x ∈ X) (hy : y ∈ X) :
    f x + ⟪gradient f x, y - x⟫_ℝ ≤ f y := by
  set d := y - x with hd
  let g : ℝ →ᵃ[ℝ] NecoaraNG.Chain.E n :=
    { toFun := fun t => x + t • d
      linear := (LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight d
      map_vadd' := by intro p v; simp [add_smul]; abel }
  have hgc : ConvexOn ℝ (g ⁻¹' X) (f ∘ g) := hf.comp_affineMap g
  have hsub : Set.Icc (0:ℝ) 1 ⊆ g ⁻¹' X := by
    intro t ht
    have := hXconv hx hy (by linarith [ht.2] : 0 ≤ 1 - t) ht.1 (by ring)
    show x + t • d ∈ X
    convert this using 1
    simp only [hd, smul_sub]
    module
  have hc : ConvexOn ℝ (Set.Icc (0:ℝ) 1) (fun t : ℝ => f (x + t • d)) :=
    (hgc.subset hsub (convex_Icc 0 1))
  have h0 : HasDerivAt (fun s : ℝ => f (x + s • d)) (⟪gradient f x, d⟫_ℝ) 0 := by
    have := line_deriv f X hdiff x d 0 (by simpa using hx)
    simpa using this
  have := hc.le_slope_of_hasDerivAt (x := 0) (y := 1) ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ zero_lt_one h0
  rw [slope_def_field] at this
  simp only [zero_smul, add_zero, one_smul, sub_zero, div_one] at this
  have e : x + d = y := by simp [hd]
  rw [e] at this
  linarith

lemma proj_ineq (X : Set (NecoaraNG.Chain.E n)) (hXconv : Convex ℝ X) (u p : NecoaraNG.Chain.E n)
    (h : NecoaraNG.Chain.IsNearest X u p) (y : NecoaraNG.Chain.E n) (hy : y ∈ X) :
    ⟪u - p, y - p⟫_ℝ ≤ 0 := by
  have hK : ‖u - p‖ = ⨅ w : X, ‖u - (w : NecoaraNG.Chain.E n)‖ := by
    have : Nonempty X := ⟨⟨p, h.1⟩⟩
    apply le_antisymm
    · exact le_ciInf (fun w => h.2 w w.2)
    · exact ciInf_le (⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩ : BddBelow (Set.range fun w : X => ‖u - (w : NecoaraNG.Chain.E n)‖)) ⟨p, h.1⟩
  exact (norm_eq_iInf_iff_real_inner_le_zero hXconv h.1).1 hK y hy

end ZZC

theorem solution {n : ℕ} (X : Set (NecoaraNG.Chain.E n)) (hXc : IsClosed X) (hXconv : Convex ℝ X)
    (f : NecoaraNG.Chain.E n → ℝ) (hf : ConvexOn ℝ X f) (hdiff : ∀ x ∈ X, DifferentiableAt ℝ f x)
    (Lf : ℝ) (hLf : 0 < Lf)
    (hL : ∀ x ∈ X, ∀ y ∈ X, ‖gradient f x - gradient f y‖ ≤ Lf * ‖x - y‖)
    (xstar : NecoaraNG.Chain.E n) (hxstar : xstar ∈ NecoaraNG.Chain.optSet X f) :
    ∀ x ∈ X, ∀ xp, NecoaraNG.ErrBound.IsPGStep X f Lf x xp → ∀ y ∈ X,
      f xp + ⟪Lf • (x - xp), y - x⟫_ℝ + 1 / (2 * Lf) * ‖Lf • (x - xp)‖ ^ 2 ≤ f y := by
  intro x hx xp hxp y hy
  have hxpX : xp ∈ X := hxp.1
  have h1 := ZZC.descent f X hXconv hdiff Lf hLf hL x xp hx hxpX
  have h2 := ZZC.gradineq f X hXconv hf hdiff x y hx hy
  have h3 := ZZC.proj_ineq X hXconv _ xp hxp y hy
  set gr := gradient f x with hgr
  have e1 : x - (1 / Lf) • gr - xp = (x - xp) - (1 / Lf) • gr := by abel
  rw [e1, inner_sub_left, real_inner_smul_left] at h3
  rw [real_inner_smul_left, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  have e2 : ⟪gr, xp - x⟫_ℝ = ⟪gr, y - x⟫_ℝ - ⟪gr, y - xp⟫_ℝ := by
    rw [← inner_sub_right]; congr 1; abel
  have e3 : ⟪x - xp, y - x⟫_ℝ = ⟪x - xp, y - xp⟫_ℝ - ‖x - xp‖ ^ 2 := by
    have : y - x = (y - xp) - (x - xp) := by abel
    rw [this, inner_sub_right, real_inner_self_eq_norm_sq]
  have e4 : ‖xp - x‖ = ‖x - xp‖ := norm_sub_rev _ _
  rw [e4] at h1
  have hB : Lf * ⟪x - xp, y - xp⟫_ℝ - ⟪gr, y - xp⟫_ℝ ≤ 0 := by
    have := mul_le_mul_of_nonneg_left h3 hLf.le
    have e : Lf * (⟪x - xp, y - xp⟫_ℝ - 1 / Lf * ⟪gr, y - xp⟫_ℝ) = Lf * ⟪x - xp, y - xp⟫_ℝ - ⟪gr, y - xp⟫_ℝ := by
      field_simp
    linarith
  have e6 : 1 / (2 * Lf) * (Lf ^ 2 * ‖x - xp‖ ^ 2) = Lf / 2 * ‖x - xp‖ ^ 2 := by field_simp
  rw [e6, e3]
  nlinarith
