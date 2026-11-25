-- Prove2me | solution 1 for GlobalTheory.T.splitCasimir_offDiagonal_norm_sq_le_of_level
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:29:33.409972+00:00
-- url     : https://prove2.me/submissions/68ce6ba2-8409-4534-b09f-056e9a41d757

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SplitCasimirOffDiagonalNormSqLeOfLevel
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_SumIoPr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SplitCasimirOffDiagonalNormSqLeOfLevelStatement
import Theorems.Thm_GlobalTheory_offDiagPart_sq_le_of_lev


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (μ : Fin n → ℝ) (kk j : ℕ) (bv : ℝ) (x : Fin n → M), IsMod ε E μ → Shape ε kk μ bv → j ≤ 4 * n ^ 2 + 2 → (∀ c, Lev ε E μ j (x c)) → ∑ b, ‖∑ c ∈ univ.erase b, E b c (x c)‖ ^ 2 ≤ (bv / 16) ^ 2 * ∑ c, ‖x c‖ ^ 2 := by
  first | exact @GlobalTheory.offDiagPart_sq_le_of_lev | exact GlobalTheory.offDiagPart_sq_le_of_lev | (intros; apply GlobalTheory.offDiagPart_sq_le_of_lev <;> assumption)
end _root_.GlobalTheory.T
