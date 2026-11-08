-- Prove2me | solution 1 for KarimiPL.ProxCD.eq_2_descent_lemma
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T21:40:12.289471+00:00
-- url     : https://prove2.me/submissions/b442f203-b9ff-4ac2-8b90-cb591bd9f9ee

import Mathlib

open scoped InnerProductSpace

theorem solution {d : ℕ} {f : EuclideanSpace ℝ (Fin d) → ℝ} {L : ℝ}
    (hf : Differentiable ℝ f)
    (hlip : ∀ x y : EuclideanSpace ℝ (Fin d), ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (x y : EuclideanSpace ℝ (Fin d)) :
    f y ≤ f x + ⟪gradient f x, y - x⟫_ℝ + L / 2 * ‖y - x‖ ^ 2 := by
  set v := y - x with hv
  have hφ : ∀ t : ℝ, HasDerivAt (fun t : ℝ => f (x + t • v)) ⟪gradient f (x + t • v), v⟫_ℝ t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => x + t • v) v t := by
      simpa using ((hasDerivAt_id' t).smul_const v).const_add x
    have h2 := (hf (x + t • v)).hasFDerivAt.comp_hasDerivAt t h1
    have e : fderiv ℝ f (x + t • v) v = ⟪gradient f (x + t • v), v⟫_ℝ := by
      rw [gradient, InnerProductSpace.toDual_symm_apply]
    rw [← e]
    exact h2
  set c := ⟪gradient f x, v⟫_ℝ with hc
  let g : ℝ → ℝ := fun t => f (x + t • v) - t * c - L / 2 * t ^ 2 * ‖v‖ ^ 2
  have hg : ∀ t : ℝ, HasDerivAt g (⟪gradient f (x + t • v), v⟫_ℝ - c - L * t * ‖v‖ ^ 2) t := by
    intro t
    have h3 := ((hφ t).sub ((hasDerivAt_id' t).mul_const c)).sub
      (((hasDerivAt_pow 2 t).const_mul (L / 2)).mul_const (‖v‖ ^ 2))
    refine h3.congr_deriv ?_
    push_cast
    ring
  have hneg : ∀ t ∈ interior (Set.Icc (0 : ℝ) 1), deriv g t ≤ 0 := by
    intro t ht
    rw [interior_Icc] at ht
    rw [(hg t).deriv]
    have h4 : ⟪gradient f (x + t • v), v⟫_ℝ - c = ⟪gradient f (x + t • v) - gradient f x, v⟫_ℝ := by
      rw [inner_sub_left]
    have h5 := real_inner_le_norm (gradient f (x + t • v) - gradient f x) v
    have h6 := hlip (x + t • v) x
    have h7 : ‖x + t • v - x‖ = t * ‖v‖ := by
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht.1]
    rw [h7] at h6
    have h8 := mul_le_mul_of_nonneg_right h6 (norm_nonneg v)
    have h9 : L * (t * ‖v‖) * ‖v‖ = L * t * ‖v‖ ^ 2 := by ring
    rw [h4]
    linarith
  have hanti : AntitoneOn g (Set.Icc 0 1) :=
    antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
      (fun t _ => (hg t).continuousAt.continuousWithinAt)
      (fun t _ => (hg t).differentiableAt.differentiableWithinAt) hneg
  have h10 := hanti ⟨le_refl 0, zero_le_one⟩ ⟨zero_le_one, le_refl 1⟩ zero_le_one
  have hg0 : g 0 = f x := by simp [g]
  have hg1 : g 1 = f y - c - L / 2 * ‖v‖ ^ 2 := by
    simp only [g, one_smul, one_mul, one_pow, mul_one]
    rw [hv, add_sub_cancel]
  rw [hg0, hg1] at h10
  linarith
