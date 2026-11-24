-- Prove2me | solution 1 for GlobalTheory.T.invariantSubspaceMobiusInverseCharpoly_of_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:24:30.818166+00:00
-- url     : https://prove2.me/submissions/37df5a5e-13cb-4669-8a67-47b22c7dc88a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvariantSubspaceMobiusInverseCharpolyOfIrreduci
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvariantSubspaceMobiusInverseCharpolyOfIrreduciStatement
import Theorems.Thm_GlobalTheory_CuspGL_psi_of_irreducible_charpoly


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
theorem _root_.solution : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (s : F[X] → ℂ), IsAdditive s → ∀ g : Module.End F V, Irreducible (LinearMap.charpoly g) → psi s V g = s (LinearMap.charpoly g) := by
  first | exact @GlobalTheory.CuspGL.psi_of_irreducible_charpoly | exact GlobalTheory.CuspGL.psi_of_irreducible_charpoly | (intros; apply GlobalTheory.CuspGL.psi_of_irreducible_charpoly <;> assumption)
end _root_.GlobalTheory.T
