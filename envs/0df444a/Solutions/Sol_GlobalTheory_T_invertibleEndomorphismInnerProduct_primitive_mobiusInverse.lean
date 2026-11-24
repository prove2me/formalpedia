-- Prove2me | solution 1 for GlobalTheory.T.invertibleEndomorphismInnerProduct_primitive_mobiusInverse
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:14:59.503851+00:00
-- url     : https://prove2.me/submissions/5913bb25-1cc2-4373-9019-16babdb96338

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvertibleEndomorphismInnerProductPrimitiveMobiu
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvertibleEndomorphismInnerProductPrimitiveMobiuStatement
import Theorems.Thm_GlobalTheory_CuspGL_PrimOrth_ipGL_psi_eq


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
theorem _root_.solution : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (s : F[X] → ℂ), IsAdditive s → ∀ φ : Module.End F V → ℂ, IsPrimitive φ → ipGL φ (psi s V) = ipGL φ (fun g => s (LinearMap.charpoly g)) := by
  first | exact @GlobalTheory.CuspGL.PrimOrth.ipGL_psi_eq | exact GlobalTheory.CuspGL.PrimOrth.ipGL_psi_eq | (intros; apply GlobalTheory.CuspGL.PrimOrth.ipGL_psi_eq <;> assumption)
end _root_.GlobalTheory.T
