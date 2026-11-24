-- Prove2me | solution 1 for GlobalTheory.T.sum_primitiveEndClassFunction_restrict_mixed_subspace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:22:16.584581+00:00
-- url     : https://prove2.me/submissions/f5d83117-752d-4b1f-9909-bbfc1afe8f55

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_SumPrimitiveEndClassFunctionRestrictMixedSubspac
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_SumPrimitiveEndClassFunctionRestrictMixedSubspacStatement
import Theorems.Thm_GlobalTheory_CuspGL_sum_restrict_eq_zero_of_mixed


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
theorem _root_.solution : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (A W : Submodule F V) (g : Module.End F V), (∀ x ∈ A, g x ∈ A) → W ⊓ A ≠ ⊥ → ¬ W ≤ A → ∀ φ : Module.End F W → ℂ, IsPrimitive φ → ∑ᶠ h : {h : Module.End F V // h ∈ nilRad A ∧ ∀ x ∈ W, (g + h) x ∈ W}, φ ((g + h.1).restrict h.2.2) = 0 := by
  first | exact @GlobalTheory.CuspGL.sum_restrict_eq_zero_of_mixed | exact GlobalTheory.CuspGL.sum_restrict_eq_zero_of_mixed | (intros; apply GlobalTheory.CuspGL.sum_restrict_eq_zero_of_mixed <;> assumption)
end _root_.GlobalTheory.T
