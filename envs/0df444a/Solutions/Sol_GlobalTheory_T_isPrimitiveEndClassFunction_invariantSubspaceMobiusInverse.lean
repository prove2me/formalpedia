-- Prove2me | solution 1 for GlobalTheory.T.isPrimitiveEndClassFunction_invariantSubspaceMobiusInverse
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:59:02.931533+00:00
-- url     : https://prove2.me/submissions/4e284a6e-2ea5-476f-b490-699a1fd4838f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsPrimitiveEndClassFunctionInvariantSubspaceMobi
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsPrimitiveEndClassFunctionInvariantSubspaceMobiStatement
import Theorems.Thm_GlobalTheory_CuspGL_isPrimitive_psi


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
theorem _root_.solution : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (s : F[X] → ℂ), IsAdditive s → IsPrimitive (psi s V) := by
  first | exact @GlobalTheory.CuspGL.isPrimitive_psi | exact GlobalTheory.CuspGL.isPrimitive_psi | (intros; apply GlobalTheory.CuspGL.isPrimitive_psi <;> assumption)
end _root_.GlobalTheory.T
