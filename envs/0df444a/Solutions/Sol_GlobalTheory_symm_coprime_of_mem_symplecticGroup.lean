-- Prove2me | solution 1 for GlobalTheory.symm_coprime_of_mem_symplecticGroup
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:46.179576+00:00
-- url     : https://prove2.me/submissions/1162c149-80eb-4045-a6ca-65c1a4c3b85c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRepresentativesQuotientRangeMulVecLin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Matrix
open GlobalTheory
variable {n : Type*} [Fintype n]
variable [DecidableEq n] {b d : Matrix n n ℤ}
namespace GlobalTheory
theorem _root_.solution {a c : Matrix n n ℤ}
    (h : fromBlocks a b c d ∈ symplecticGroup n ℤ) :
    (dᵀ * b).IsSymm ∧ ∃ u v : Matrix n n ℤ, u * b + v * d = 1 := by
  rw [SymplecticGroup.mem_iff', J, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply,
    fromBlocks_inj] at h
  obtain ⟨-, h1, -, h2⟩ := h
  simp only [Matrix.mul_zero, Matrix.mul_one, zero_add, add_zero, Matrix.mul_neg,
    Matrix.neg_mul] at h1 h2
  refine ⟨?_, -cᵀ, aᵀ, ?_⟩
  · rw [Matrix.IsSymm, transpose_mul, transpose_transpose]
    exact (add_neg_eq_zero.1 h2).symm
  · rw [← neg_inj, ← h1, Matrix.neg_mul, neg_add, neg_neg]
end GlobalTheory
