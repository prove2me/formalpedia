-- Prove2me | solution 1 for GlobalTheory.T.finsum_subspaceStabilizer_mul_block_functions
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:09:41.211951+00:00
-- url     : https://prove2.me/submissions/6677eb00-150f-4d96-835b-706503b85adc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FinsumSubspaceStabilizerMulBlockFunctions
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FinsumSubspaceStabilizerMulBlockFunctionsStatement
import Theorems.Thm_GlobalTheory_CuspGL_finsum_stabiliser_mul_blocks


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
theorem _root_.solution : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (W : Submodule F V) (Φ : Module.End F W → ℂ) (Φ' : Module.End F (V ⧸ W) → ℂ), ∑ᶠ g : {g : Module.End F V // ∀ x ∈ W, g x ∈ W}, Φ (g.1.restrict g.2) * Φ' (W.mapQ W g.1 (fun x hx => g.2 x hx)) = (Nat.card F : ℂ) ^ (Module.finrank F W * Module.finrank F (V ⧸ W)) * ((∑ᶠ a, Φ a) * ∑ᶠ b, Φ' b) := by
  first | exact @GlobalTheory.CuspGL.finsum_stabiliser_mul_blocks | exact GlobalTheory.CuspGL.finsum_stabiliser_mul_blocks | (intros; apply GlobalTheory.CuspGL.finsum_stabiliser_mul_blocks <;> assumption)
end _root_.GlobalTheory.T
