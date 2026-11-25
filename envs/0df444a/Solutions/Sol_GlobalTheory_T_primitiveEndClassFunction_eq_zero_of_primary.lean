-- Prove2me | solution 1 for GlobalTheory.T.primitiveEndClassFunction_eq_zero_of_primary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:24:24.040945+00:00
-- url     : https://prove2.me/submissions/96799732-ffa1-4d1f-b126-52ed21e3b2a8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_PrimitiveEndClassFunctionEqZeroOfPrimary
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_PrimitiveEndClassFunctionEqZeroOfPrimaryStatement
import Theorems.Thm_GlobalTheory_CuspGL_primitive_eq_zero_of_primary


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
theorem _root_.solution : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (φ : Module.End F V → ℂ), IsClassFn φ → IsPrimitive φ → ∀ (f : F[X]) (m : ℕ), Irreducible f → (∀ g : Module.End F V, LinearMap.charpoly g = f ^ m → aeval g f = 0 → φ g = 0) → ∀ g : Module.End F V, LinearMap.charpoly g = f ^ m → φ g = 0 := by
  first | exact @GlobalTheory.CuspGL.primitive_eq_zero_of_primary | exact GlobalTheory.CuspGL.primitive_eq_zero_of_primary | (intros; apply GlobalTheory.CuspGL.primitive_eq_zero_of_primary <;> assumption)
end _root_.GlobalTheory.T
