-- Prove2me | solution 1 for GlobalTheory.T.exists_common_eigenvector_mem_of_commute
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:18:25.26638+00:00
-- url     : https://prove2.me/submissions/5bad03f4-abc5-46e3-8612-95293bf927c0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MatrixExistsCommonEigenvectorMem
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MatrixExistsCommonEigenvectorMemStatement
import Theorems.Thm_GlobalTheory_matrix_exists_common_eigenvector_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : Type) [Field K] [IsAlgClosed K] (n : ℕ) (S : Set (Matrix (Fin n) (Fin n) K)), (∀ A ∈ S, ∀ B ∈ S, Commute A B) → ∀ (E : Submodule K (Fin n → K)), E ≠ ⊥ → (∀ A ∈ S, ∀ v ∈ E, A *ᵥ v ∈ E) → ∃ v ∈ E, v ≠ 0 ∧ ∀ A ∈ S, ∃ μ : K, A *ᵥ v = μ • v := by
  first | exact @GlobalTheory.matrix_exists_common_eigenvector_mem | exact GlobalTheory.matrix_exists_common_eigenvector_mem | (intros; apply GlobalTheory.matrix_exists_common_eigenvector_mem <;> assumption)
end _root_.GlobalTheory.T
