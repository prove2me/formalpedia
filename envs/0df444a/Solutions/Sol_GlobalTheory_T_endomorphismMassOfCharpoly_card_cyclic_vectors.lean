-- Prove2me | solution 1 for GlobalTheory.T.endomorphismMassOfCharpoly_card_cyclic_vectors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:06:51.65338+00:00
-- url     : https://prove2.me/submissions/b017e7ed-cbba-4aa3-a485-10d51b190469

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EndomorphismMassOfCharpolyCardCyclicVectors
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EndomorphismMassOfCharpolyCardCyclicVectorsStatement
import Theorems.Thm_GlobalTheory_CuspGL_mass_card_cyclic


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
theorem _root_.solution : ∀ (F : Type) [Field F] [Finite F] (D : F[X]), D.Monic → mass (fun g : Module.End F (Fin D.natDegree → F) => (Nat.card {v : Fin D.natDegree → F // ∀ U : Submodule F (Fin D.natDegree → F), (∀ x ∈ U, g x ∈ U) → v ∈ U → U = ⊤} : ℂ)) D = glCard F D.natDegree := by
  first | exact @GlobalTheory.CuspGL.mass_card_cyclic | exact GlobalTheory.CuspGL.mass_card_cyclic | (intros; apply GlobalTheory.CuspGL.mass_card_cyclic <;> assumption)
end _root_.GlobalTheory.T
