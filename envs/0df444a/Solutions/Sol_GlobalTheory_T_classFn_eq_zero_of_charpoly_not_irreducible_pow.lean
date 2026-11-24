-- Prove2me | solution 1 for GlobalTheory.T.classFn_eq_zero_of_charpoly_not_irreducible_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:04:44.670043+00:00
-- url     : https://prove2.me/submissions/d2a9d7a3-33d4-497b-8609-f0d54b955b37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EqZeroOfNotPrimary
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EqZeroOfNotPrimaryStatement
import Theorems.Thm_GlobalTheory_CuspGL_eq_zero_of_not_primary


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
theorem _root_.solution : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (φ : Module.End F V → ℂ), IsClassFn φ → IsPrimitive φ → 0 < Module.finrank F V → ∀ g : Module.End F V, (¬ ∃ (f : F[X]) (m : ℕ), f.Monic ∧ Irreducible f ∧ 0 < m ∧ LinearMap.charpoly g = f ^ m) → φ g = 0 := by
  first | exact @GlobalTheory.CuspGL.eq_zero_of_not_primary | exact GlobalTheory.CuspGL.eq_zero_of_not_primary | (intros; apply GlobalTheory.CuspGL.eq_zero_of_not_primary <;> assumption)
end _root_.GlobalTheory.T
