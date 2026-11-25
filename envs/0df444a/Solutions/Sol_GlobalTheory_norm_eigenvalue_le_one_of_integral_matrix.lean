-- Prove2me | solution 1 for GlobalTheory.norm_eigenvalue_le_one_of_integral_matrix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:40:42.315938+00:00
-- url     : https://prove2.me/submissions/87a497d3-9b32-4f62-9f5f-da54b4512007

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormEigenvalueLeOneOfIntegralMatrixUltrametric

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (O K : Type) [CommRing O] [NormedField K]
    [IsUltrametricDist K] (emb : O →+* K) (hemb : ∀ c, ‖emb c‖ ≤ 1) (n : ℕ)
    (M : Matrix (Fin n) (Fin n) O) (μ : K) (c : Fin n → K) (hc : c ≠ 0)
    (hM : (M.map emb).mulVec c = μ • c) : ‖μ‖ ≤ 1 := by
  obtain ⟨j₀, hj₀⟩ : ∃ j, c j ≠ 0 := by
    by_contra h
    push_neg at h
    exact hc (funext h)
  obtain ⟨k, -, hk⟩ := Finset.exists_max_image Finset.univ (fun j => ‖c j‖) ⟨j₀, Finset.mem_univ _⟩
  have hpos : 0 < ‖c k‖ :=
    lt_of_lt_of_le (norm_pos_iff.2 hj₀) (hk j₀ (Finset.mem_univ _))
  have hrow : (M.map emb).mulVec c k = μ * c k := by
    rw [hM]; simp
  have hsum : ‖(M.map emb).mulVec c k‖ ≤ ‖c k‖ := by
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun j _ => ?_
    rw [norm_mul]
    calc ‖emb (M k j)‖ * ‖c j‖ ≤ 1 * ‖c k‖ :=
          mul_le_mul (hemb _) (hk j (Finset.mem_univ _)) (norm_nonneg _) zero_le_one
      _ = ‖c k‖ := one_mul _
  rw [hrow, norm_mul] at hsum
  have : ‖μ‖ * ‖c k‖ ≤ 1 * ‖c k‖ := by rwa [one_mul]
  exact le_of_mul_le_mul_right this hpos
end GlobalTheory
