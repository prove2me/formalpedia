-- Prove2me | solution 1 for Kakutani1941.FixedPoint.retraction
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T09:19:17.670134+00:00
-- url     : https://prove2.me/submissions/212acd64-862d-4661-9547-7057f58dee29

import Mathlib
namespace Kakutani1941.FixedPoint

open RealInnerProductSpace in
theorem retraction {m : ℕ} {S T : Set (EuclideanSpace ℝ (Fin m))}
    (hSclosed : IsClosed S) (hSconvex : Convex ℝ S) (hSnonempty : S.Nonempty)
    (hST : S ⊆ T) :
    ∃ ψ : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m),
      ContinuousOn ψ T ∧ Set.MapsTo ψ T S ∧ ∀ x ∈ S, ψ x = x := by
  have hex := exists_norm_eq_iInf_of_complete_convex hSnonempty hSclosed.isComplete hSconvex
  choose ψ hψS hψmin using hex
  have hvar : ∀ u, ∀ w ∈ S, ⟪u - ψ u, w - ψ u⟫ ≤ 0 := fun u =>
    (norm_eq_iInf_iff_real_inner_le_zero hSconvex (hψS u)).1 (hψmin u)
  have hfix : ∀ x ∈ S, ψ x = x := by
    intro x hx
    have h := hvar x x hx
    rw [real_inner_self_eq_norm_sq] at h
    have : ‖x - ψ x‖ = 0 := by nlinarith [norm_nonneg (x - ψ x)]
    exact (sub_eq_zero.1 (norm_eq_zero.1 this)).symm
  have hlip : LipschitzWith 1 ψ := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    simp only [NNReal.coe_one, one_mul, dist_eq_norm]
    have h1 := hvar x (ψ y) (hψS y)
    have h2 := hvar y (ψ x) (hψS x)
    have key : ‖ψ x - ψ y‖ ^ 2 ≤ ⟪x - y, ψ x - ψ y⟫ := by
      have e1 : ⟪x - ψ x, ψ y - ψ x⟫ + ⟪y - ψ y, ψ x - ψ y⟫
          = ‖ψ x - ψ y‖ ^ 2 - ⟪x - y, ψ x - ψ y⟫ := by
        rw [← real_inner_self_eq_norm_sq]
        have : ψ y - ψ x = -(ψ x - ψ y) := by abel
        rw [this, inner_neg_right]
        simp only [inner_sub_left, inner_sub_right]
        ring
      linarith
    have cs := real_inner_le_norm (x - y) (ψ x - ψ y)
    rcases eq_or_lt_of_le (norm_nonneg (ψ x - ψ y)) with h0 | h0
    · rw [← h0]; exact norm_nonneg _
    · nlinarith
  exact ⟨ψ, hlip.continuous.continuousOn, fun x _ => hψS x, hfix⟩

end Kakutani1941.FixedPoint

theorem solution {m : ℕ} {S T : Set (EuclideanSpace ℝ (Fin m))}
    (hSclosed : IsClosed S) (hSconvex : Convex ℝ S) (hSnonempty : S.Nonempty)
    (hST : S ⊆ T) :
    ∃ ψ : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m),
      ContinuousOn ψ T ∧ Set.MapsTo ψ T S ∧ ∀ x ∈ S, ψ x = x :=
  Kakutani1941.FixedPoint.retraction hSclosed hSconvex hSnonempty hST
