-- Prove2me | solution 1 for GlobalTheory.WeightedInverseBound.bound_one_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:51:27.311845+00:00
-- url     : https://prove2.me/submissions/f84ea627-3dab-4ee7-8698-02f2503fe8fa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeightedLeastSquaresBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SmulInvMulPosSemidefUniformBound
import Theorems.Thm_GlobalTheory_WeightedInverseBound_wls_fintype
import Theorems.Thm_GlobalTheory_WeightedInverseBound_norm_mulVec_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ComplexOrder Matrix
open GlobalTheory
open GlobalTheory.WeightedInverseBound
namespace GlobalTheory.WeightedInverseBound
theorem _root_.solution {g a : ℕ} (B : Fin a → Matrix (Fin g) (Fin g) ℝ)
    (hB : ∀ i, (B i).PosSemidef) : ∃ K : ℝ, ∀ t : Fin a → ℝ, (∀ i, 0 < t i) → ∀ i x,
      ‖(1 + ∑ l, t l • B l)⁻¹.mulVec ((t i • B i).mulVec x)‖ ≤ K * ‖x‖ := by
  classical
  have hR : ∀ i, ∃ R : Matrix (Fin g) (Fin g) ℝ, B i = R.transpose * R := by
    intro i
    open scoped MatrixOrder in
    obtain ⟨R, hR⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.1 (hB i).nonneg
    exact ⟨R, by rw [hR]; rfl⟩
  choose R hR using hR
  let L : Matrix (Fin g ⊕ (Fin a × Fin g)) (Fin g) ℝ :=
    Matrix.fromRows 1 (Matrix.of fun p j => R p.1 p.2 j)
  have hL : L.rank = g := by
    refine le_antisymm (by simpa using L.rank_le_card_width) ?_
    have h1 : (Matrix.fromCols (1 : Matrix (Fin g) (Fin g) ℝ)
        (0 : Matrix (Fin g) (Fin a × Fin g) ℝ)) * L = 1 := by
      simp [L, Matrix.fromCols_mul_fromRows]
    have h2 := Matrix.rank_mul_le_right (Matrix.fromCols (1 : Matrix (Fin g) (Fin g) ℝ)
        (0 : Matrix (Fin g) (Fin a × Fin g) ℝ)) L
    rw [h1, Matrix.rank_one, Fintype.card_fin] at h2
    exact h2
  obtain ⟨K, hK⟩ := wls_fintype L hL
  obtain ⟨A, hA0, hA⟩ : ∃ A : ℝ, 0 ≤ A ∧ ∀ i j k, |R i j k| ≤ A :=
    ⟨‖fun i j k => R i j k‖, norm_nonneg _, fun i j k =>
      ((norm_le_pi_norm _ k).trans (norm_le_pi_norm (fun j k => R i j k) j)).trans
        (norm_le_pi_norm (fun i j k => R i j k) i)⟩
  refine ⟨|K| * (g * A), fun t ht i x => ?_⟩
  let D : Fin g ⊕ (Fin a × Fin g) → ℝ := Sum.elim (fun _ => 1) (fun p => t p.1)
  let b : Fin g ⊕ (Fin a × Fin g) → ℝ :=
    Sum.elim (fun _ => 0) (fun p => if p.1 = i then (R i).mulVec x p.2 else 0)
  have hD : ∀ k, 0 < D k := by
    rintro (k | p)
    · exact one_pos
    · exact ht _
  have h := hK D b hD
  have h1 : L.transpose * Matrix.diagonal D * L = 1 + ∑ l, t l • B l := by
    ext j k
    simp only [Matrix.mul_apply (M := _ * Matrix.diagonal _), Matrix.mul_diagonal,
      Matrix.transpose_apply, Fintype.sum_sum_type, Fintype.sum_prod_type, L, D,
      Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Sum.elim_inl, Sum.elim_inr,
      Matrix.of_apply, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, hR,
      Matrix.mul_apply (N := R _), smul_eq_mul, Finset.mul_sum]
    congr 1
    · simp [Matrix.one_apply, eq_comm]
    · exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => by ring
  have h2 : (L.transpose * Matrix.diagonal D).mulVec b = (t i • B i).mulVec x := by
    rw [hR i, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec x]
    ext j
    simp only [Matrix.mulVec, dotProduct, Matrix.mul_diagonal,
      Matrix.transpose_apply, Fintype.sum_sum_type, Fintype.sum_prod_type, L, D, b,
      Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Sum.elim_inl, Sum.elim_inr,
      Matrix.of_apply, Pi.smul_apply, smul_eq_mul, mul_zero, Finset.sum_const_zero, zero_add]
    rw [Finset.sum_eq_single i]
    · simp only [if_true]
      rw [Finset.mul_sum Finset.univ _ (t i)]
      exact Finset.sum_congr rfl fun m _ => by ring
    · intro l _ hl
      simp [hl]
    · simp
  have h3 : ‖b‖ ≤ g * A * ‖x‖ := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 ?_
    rintro (k | p)
    · simp only [b, Sum.elim_inl, norm_zero]; positivity
    · simp only [b, Sum.elim_inr]
      split_ifs
      · exact (norm_le_pi_norm _ _).trans (norm_mulVec_le hA0 (hA i) x)
      · simp only [norm_zero]; positivity
  rw [h1, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, h2] at h
  calc _ ≤ K * ‖b‖ := h
    _ ≤ |K| * ‖b‖ := mul_le_mul_of_nonneg_right (le_abs_self K) (norm_nonneg _)
    _ ≤ |K| * (g * A * ‖x‖) := mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
    _ = _ := by ring
end GlobalTheory.WeightedInverseBound
