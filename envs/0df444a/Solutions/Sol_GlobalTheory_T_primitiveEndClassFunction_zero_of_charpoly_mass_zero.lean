-- Prove2me | solution 1 for GlobalTheory.T.primitiveEndClassFunction_zero_of_charpoly_mass_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:03:10.444806+00:00
-- url     : https://prove2.me/submissions/cb6dbe27-815b-4abc-b5ac-9ea599e4af32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_PrimitiveEndClassFunctionZeroOfCharpolyMassZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_PrimitiveEndClassFunctionZeroOfCharpolyMassZeroStatement
import Theorems.Thm_GlobalTheory_CuspGL_eq_zero_of_mass_charpoly_eq_zero


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
theorem _root_.solution : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (φ : Module.End F V → ℂ), IsClassFn φ → IsPrimitive φ → ∀ g : Module.End F V, mass φ (LinearMap.charpoly g) = 0 → φ g = 0 := by
  first | exact @GlobalTheory.CuspGL.eq_zero_of_mass_charpoly_eq_zero | exact GlobalTheory.CuspGL.eq_zero_of_mass_charpoly_eq_zero | (intros; apply GlobalTheory.CuspGL.eq_zero_of_mass_charpoly_eq_zero <;> assumption)
end _root_.GlobalTheory.T
