-- Prove2me | solution 1 for LewisTorczon.BoundPS.proposition_4_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:51:43.333687+00:00
-- url     : https://prove2.me/submissions/c363594a-df4b-4a22-9a14-77ccb1f4ea48

import Mathlib
import Definitions.Def_LewisTorczon_BoundPS_Box
import Definitions.Def_LewisTorczon_BoundPS_ProjQ
import Definitions.Def_LewisTorczon_BoundPS_GPS

namespace LewisTorczon.BoundPS

theorem aux_p41_seg {n : ℕ} (x d : EuclideanSpace ℝ (Fin n)) (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    x + t • d ∈ segment ℝ x (x + d) := by
  rw [segment_eq_image']
  exact ⟨t, ht, by simp⟩

end LewisTorczon.BoundPS

open LewisTorczon.BoundPS

theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x d : EuclideanSpace ℝ (Fin n)) (ε δ : ℝ) (hε : 0 < ε)
    (hdiff : ∀ y ∈ segment ℝ x (x + d), DifferentiableAt ℝ f y)
    (hcont : ContinuousOn (gradient f) (segment ℝ x (x + d)))
    (hgx : gradient f x ≠ 0) (hdesc : inner ℝ (gradient f x) d ≤ -ε * ‖d‖)
    (hω : ∀ y, ‖y - x‖ < δ → ‖gradient f y - gradient f x‖ < ε / 2) (hd : ‖d‖ < δ) :
    f (x + d) - f x ≤ -(ε / 2) * ‖d‖ := by
  have hderiv : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt (fun s : ℝ => f (x + s • d))
      (inner ℝ (gradient f (x + t • d)) d) t := by
    intro t ht
    have h1 : HasFDerivAt f (fderiv ℝ f (x + t • d)) (x + t • d) :=
      (hdiff _ (aux_p41_seg x d t ht)).hasFDerivAt
    have h2 : HasDerivAt (fun s : ℝ => x + s • d) d t := by
      simpa using ((hasDerivAt_id t).smul_const d).const_add x
    have := h1.comp_hasDerivAt t h2
    have key : inner ℝ (gradient f (x + t • d)) d = (fderiv ℝ f (x + t • d)) d :=
      InnerProductSpace.toDual_symm_apply
    rw [key]
    exact this
  obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope (fun s : ℝ => f (x + s • d))
    (fun t => inner ℝ (gradient f (x + t • d)) d) zero_lt_one
    (fun t ht => (hderiv t ht).continuousAt.continuousWithinAt)
    (fun t ht => hderiv t (Set.Ioo_subset_Icc_self ht))
  simp only [one_smul, zero_smul, add_zero, sub_zero, div_one] at hξeq
  rw [← hξeq]
  have hξ0 : 0 ≤ ξ := hξ.1.le
  have hξ1 : ξ ≤ 1 := hξ.2.le
  have hnorm : ‖(x + ξ • d) - x‖ < δ := by
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hξ0]
    calc ξ * ‖d‖ ≤ 1 * ‖d‖ := by gcongr
      _ = ‖d‖ := one_mul _
      _ < δ := hd
  have hg := hω _ hnorm
  have hsplit : inner ℝ (gradient f (x + ξ • d)) d
      = inner ℝ (gradient f x) d + inner ℝ (gradient f (x + ξ • d) - gradient f x) d := by
    rw [inner_sub_left]; ring
  have hcs : inner ℝ (gradient f (x + ξ • d) - gradient f x) d
      ≤ ‖gradient f (x + ξ • d) - gradient f x‖ * ‖d‖ := real_inner_le_norm _ _
  have hdn : 0 ≤ ‖d‖ := norm_nonneg _
  have : ‖gradient f (x + ξ • d) - gradient f x‖ * ‖d‖ ≤ ε / 2 * ‖d‖ := by
    gcongr
  rw [hsplit]
  linarith
