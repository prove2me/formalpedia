-- Prove2me | solution 1 for GlobalTheory.T.eq_zero_of_pow_eq_zero_of_mem_adjoin_of_charpoly_separable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:14:41.743343+00:00
-- url     : https://prove2.me/submissions/f4f6fe44-fc36-47ca-8e2f-b50b056ad3f4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdjoinMatrixReducedOfCharpolySeparable
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdjoinMatrixReducedOfCharpolySeparableStatement
import Theorems.Thm_GlobalTheory_adjoin_matrix_reduced_of_charpoly_separable


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Polynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : Type) [Field K] (n : ℕ) (N : Matrix (Fin n) (Fin n) K), N.charpoly.Separable → ∀ g ∈ Algebra.adjoin K {N}, ∀ m : ℕ, g ^ m = 0 → g = 0 := by
  first | exact @GlobalTheory.adjoin_matrix_reduced_of_charpoly_separable | exact GlobalTheory.adjoin_matrix_reduced_of_charpoly_separable | (intros; apply GlobalTheory.adjoin_matrix_reduced_of_charpoly_separable <;> assumption)
end _root_.GlobalTheory.T
