-- Prove2me | solution 1 for GlobalTheory.T.isCharacter_cuspidal_rootSum_regular
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:03:01.887094+00:00
-- url     : https://prove2.me/submissions/5e9f3161-62f6-4e5c-a319-217572ded70e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterCuspidalRootSumRegular
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterCuspidalRootSumRegularStatement
import Theorems.Thm_GlobalTheory_CuspGL_isChar_psi_rootSum_of_regular


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
theorem _root_.solution : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ), (∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ d k : ℕ, 0 < d → (∀ i : ℕ, 0 < i → i < d → ¬ k * Nat.card F ^ i ≡ k [MOD Nat.card F ^ d - 1]) → IsChar ℂ ℂ (fun x : GL (Fin d) F => (-1) ^ (d - 1) * psi (rootSum θ k) (Fin d → F) (Matrix.toLin' (x : Matrix (Fin d) (Fin d) F))) ∧ ipGL (psi (rootSum θ k) (Fin d → F)) (psi (rootSum θ k) (Fin d → F)) = glCard F d := by
  first | exact @GlobalTheory.CuspGL.isChar_psi_rootSum_of_regular | exact GlobalTheory.CuspGL.isChar_psi_rootSum_of_regular | (intros; apply GlobalTheory.CuspGL.isChar_psi_rootSum_of_regular <;> assumption)
end _root_.GlobalTheory.T
