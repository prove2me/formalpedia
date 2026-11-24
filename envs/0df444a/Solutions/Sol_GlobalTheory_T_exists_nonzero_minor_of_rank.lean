-- Prove2me | solution 1 for GlobalTheory.T.exists_nonzero_minor_of_rank
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:03:27.068159+00:00
-- url     : https://prove2.me/submissions/75b6a889-58de-4291-ad8c-c9db4796e98b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsNonzeroMinorOfRank
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsNonzeroMinorOfRankStatement
import Theorems.Thm_GlobalTheory_exists_submatrix_det_ne_zero_of_le_rank


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
theorem _root_.solution : ∀ (k : Type) [Field k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ρ : ℕ) (Y : Matrix A D k), ρ ≤ Y.rank → ∃ S : Fin ρ → A, ∃ τ : Fin ρ → D, (Y.submatrix S τ).det ≠ 0 := by
  first | exact @GlobalTheory.exists_submatrix_det_ne_zero_of_le_rank | exact GlobalTheory.exists_submatrix_det_ne_zero_of_le_rank | (intros; apply GlobalTheory.exists_submatrix_det_ne_zero_of_le_rank <;> assumption)
end _root_.GlobalTheory.T
