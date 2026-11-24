-- Prove2me | solution 1 for GlobalTheory.BI.invariant_eq_top_of_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:59:10.733637+00:00
-- url     : https://prove2.me/submissions/69e3b413-42bd-4430-8dbf-47c4ccc55e53

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CommuteImageAbelianByPrimePowerOfNormalCentral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsCharacterEigenvectorOfCommutingRepresentat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvariantEqTopOfIrreducible

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory GlobalTheory.BI
namespace GlobalTheory.BI
theorem _root_.solution {k : Type} [Field k] {G : Type} [Group G] {V : Type}
    [AddCommGroup V] [Module k V] (ρ : Representation k G V) (h : ρ.IsIrreducible)
    (U : Submodule k V) (hU : ∀ g, ∀ v ∈ U, ρ g v ∈ U) (v : V) (hv : v ∈ U) (hv0 : v ≠ 0) :
    U = ⊤ := by
  rcases h.eq_bot_or_eq_top (⟨U, fun g v hv => hU g v hv⟩ : Subrepresentation ρ) with H | H
  · have H' : U = ⊥ := congrArg Subrepresentation.toSubmodule H
    exact absurd (by simpa [H'] using hv) hv0
  · exact congrArg Subrepresentation.toSubmodule H
end GlobalTheory.BI
