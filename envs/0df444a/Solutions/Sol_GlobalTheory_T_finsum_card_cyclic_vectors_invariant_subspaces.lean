-- Prove2me | solution 1 for GlobalTheory.T.finsum_card_cyclic_vectors_invariant_subspaces
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:09:32.930279+00:00
-- url     : https://prove2.me/submissions/a44b39bb-2057-4d18-8cfd-927fdd9a4973

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FinsumCardCyclicVectorsInvariantSubspaces
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FinsumCardCyclicVectorsInvariantSubspacesStatement
import Theorems.Thm_GlobalTheory_CuspGL_finsum_card_cyclic_eq


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
theorem _root_.solution : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (g : Module.End F V), ∑ᶠ W : {W : Submodule F V // ∀ x ∈ W, g x ∈ W}, (Nat.card {v : W.1 // ∀ U : Submodule F (W.1), (∀ x ∈ U, (g.restrict W.2) x ∈ U) → v ∈ U → U = ⊤} : ℂ) = (Nat.card F : ℂ) ^ Module.finrank F V := by
  first | exact @GlobalTheory.CuspGL.finsum_card_cyclic_eq | exact GlobalTheory.CuspGL.finsum_card_cyclic_eq | (intros; apply GlobalTheory.CuspGL.finsum_card_cyclic_eq <;> assumption)
end _root_.GlobalTheory.T
