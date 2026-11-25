-- Prove2me | solution 1 for GlobalTheory.ParabVirt.mem_stab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:03:25.455927+00:00
-- url     : https://prove2.me/submissions/90435a2d-562d-4683-b52a-83b72b688b8d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_VirtualCharactersMulComapConjIndLinearStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ParabolicInductionTrivialPreservesVirtualCharact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
noncomputable section
open GlobalTheory GlobalTheory.ParabVirt
variable {F : Type} [Field F] {n : ℕ}
open Polynomial
variable {F : Type} [Field F] {n : ℕ}
namespace GlobalTheory.ParabVirt
namespace _root_.GlobalTheory.ParabVirt
theorem _root_.solution (W : Submodule F (Fin n → F)) (x : GL (Fin n) F) :
    x ∈ _root_.GlobalTheory.ParabVirt.stab W ↔
      ∀ v ∈ W, Matrix.toLin' (x : Matrix (Fin n) (Fin n) F) v ∈ W := Iff.rfl
end _root_.GlobalTheory.ParabVirt
end GlobalTheory.ParabVirt
