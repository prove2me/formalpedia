-- Prove2me | solution 1 for GlobalTheory.T.invariantSubspaceMobiusInverse_one_prod_Ico
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:11:42.304937+00:00
-- url     : https://prove2.me/submissions/c66d8ba4-48f6-4193-b547-7ed2193a6df9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvariantSubspaceMobiusInverseOneProdIco
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvariantSubspaceMobiusInverseOneProdIcoStatement
import Theorems.Thm_GlobalTheory_CuspGL_psi_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (s : F[X] → ℂ), (∀ j : ℕ, s ((X - C 1) ^ j) = j) → 0 < Module.finrank F V → psi s V 1 = ∏ i ∈ Finset.Ico 1 (Module.finrank F V), (1 - (Nat.card F : ℂ) ^ i) := by
  first | exact @GlobalTheory.CuspGL.psi_one | exact GlobalTheory.CuspGL.psi_one | (intros; apply GlobalTheory.CuspGL.psi_one <;> assumption)
end _root_.GlobalTheory.T
