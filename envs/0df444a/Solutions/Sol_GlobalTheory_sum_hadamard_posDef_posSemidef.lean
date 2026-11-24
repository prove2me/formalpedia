-- Prove2me | solution 1 for GlobalTheory.sum_hadamard_posDef_posSemidef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:36:14.529499+00:00
-- url     : https://prove2.me/submissions/877b4591-9bea-4eef-b985-67e8e5aac690

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SumHadamardPosDefPosSemidef

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Matrix
namespace GlobalTheory
theorem _root_.solution :
    ∀ {r : ℕ} (S G : Matrix (Fin r) (Fin r) ℝ), S.PosDef → G.PosSemidef →
      0 ≤ ∑ i, ∑ j, S i j * G i j ∧ (G ≠ 0 → 0 < ∑ i, ∑ j, S i j * G i j) := by
  intro r S G hS hG
  obtain ⟨m, v, rfl⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hG
  have key : ∑ i, ∑ j, S i j * (∑ k, vecMulVec (v k) (star (v k))) i j
      = ∑ k, star (v k) ⬝ᵥ (S *ᵥ v k) := by
    simp only [Matrix.sum_apply, Finset.sum_apply, vecMulVec_apply, Pi.star_apply, star_trivial, dotProduct,
      mulVec, Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have term : ∀ k, 0 ≤ star (v k) ⬝ᵥ (S *ᵥ v k) := fun k =>
    hS.posSemidef.dotProduct_mulVec_nonneg _
  rw [key]
  refine ⟨Finset.sum_nonneg fun k _ => term k, fun hne => ?_⟩
  have : ∃ k, v k ≠ 0 := by
    by_contra h
    push_neg at h
    apply hne
    simp [h]
  obtain ⟨k, hk⟩ := this
  exact Finset.sum_pos' (fun k _ => term k) ⟨k, Finset.mem_univ _, hS.dotProduct_mulVec_pos hk⟩
end GlobalTheory
