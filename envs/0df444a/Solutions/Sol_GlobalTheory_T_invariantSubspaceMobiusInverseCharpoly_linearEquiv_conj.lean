-- Prove2me | solution 1 for GlobalTheory.T.invariantSubspaceMobiusInverseCharpoly_linearEquiv_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:40:56.573872+00:00
-- url     : https://prove2.me/submissions/115eab58-0098-4c4c-950f-593c5bacc014

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvariantSubspaceMobiusInverseCharpolyLinearEqui
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvariantSubspaceMobiusInverseCharpolyLinearEquiStatement
import Theorems.Thm_GlobalTheory_CuspGL_psi_conj


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
theorem _root_.solution : ∀ (F : Type) [Field F] (s : F[X] → ℂ) (V V' : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] [AddCommGroup V'] [Module F V'] [FiniteDimensional F V'] (e : V ≃ₗ[F] V') (g : Module.End F V), psi s V' (e.conj g) = psi s V g := by
  first | exact @GlobalTheory.CuspGL.psi_conj | exact GlobalTheory.CuspGL.psi_conj | (intros; apply GlobalTheory.CuspGL.psi_conj <;> assumption)
end _root_.GlobalTheory.T
