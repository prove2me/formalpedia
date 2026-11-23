-- Prove2me | solution 1 for GlobalTheory.T.rootPowerSumCharacter_additive_and_X_sub_one_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:37:06.129337+00:00
-- url     : https://prove2.me/submissions/0c95363a-841e-49a1-9109-7fd7135a4876

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_RootPowerSumCharacterAdditiveAndXSubOnePow
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_RootPowerSumCharacterAdditiveAndXSubOnePowStatement
import Theorems.Thm_GlobalTheory_CuspGL_rootSum_isAdditive_and_pow_X_sub_one


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
theorem _root_.solution : ∀ (F : Type) [Field F] (θ : AlgebraicClosure F →* ℂ) (k : ℕ), IsAdditive (rootSum θ k) ∧ ∀ j : ℕ, rootSum θ k ((X - C 1 : F[X]) ^ j) = j := by
  first | exact @GlobalTheory.CuspGL.rootSum_isAdditive_and_pow_X_sub_one | exact GlobalTheory.CuspGL.rootSum_isAdditive_and_pow_X_sub_one | (intros; apply GlobalTheory.CuspGL.rootSum_isAdditive_and_pow_X_sub_one <;> assumption)
end _root_.GlobalTheory.T
