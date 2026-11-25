-- Prove2me | solution 1 for GlobalTheory.T.parseval_bound_integerVector_smallFourierSupport
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:51:31.30436+00:00
-- url     : https://prove2.me/submissions/730c1bd5-ea53-45b2-a602-57e571d7ff97

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ParsevalBoundIntegerVectorSmallFourierSupport
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ParsevalBoundIntegerVectorSmallFourierSupportStatement
import Theorems.Thm_GlobalTheory_parsevalSep_bound


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (n N : ℕ) (ω : ℂ) (c : ℕ → ℤ) (S : Finset ℕ), 0 < n → 0 < N → IsPrimitiveRoot ω N → ∑ k ∈ Finset.range N, c k ^ 2 = 2 * n → |∑ k ∈ Finset.range N, c k| ≤ (n : ℤ) - 1 → (∀ j : ℕ, 0 < j → j < N → j ∉ S → ∑ k ∈ Finset.range N, (c k : ℂ) * ω ^ (j * k) = 0) → 2 * n * N ≤ (n - 1) ^ 2 + 4 * n ^ 2 * S.card := by
  first | exact @GlobalTheory.parsevalSep_bound | exact GlobalTheory.parsevalSep_bound | (intros; apply GlobalTheory.parsevalSep_bound <;> assumption)
end _root_.GlobalTheory.T
