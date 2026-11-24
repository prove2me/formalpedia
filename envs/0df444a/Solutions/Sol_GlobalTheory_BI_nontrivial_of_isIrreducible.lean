-- Prove2me | solution 1 for GlobalTheory.BI.nontrivial_of_isIrreducible
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:26:43.157919+00:00
-- url     : https://prove2.me/submissions/9f45512d-ecb0-4ac8-9bdc-a05e87b14c1e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CommuteImageAbelianByPrimePowerOfNormalCentralStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsCharacterEigenvectorOfCommutingRepresentatStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CharacterEqInducedOfImprimitivitySystemStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IrreducibleIdempotentEqOneAndCharacterEqWeightAlStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsWeightIdempotentStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IrreducibleCharacterLinearOrInducedAbelianByPrim

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.BI
open GlobalTheory GlobalTheory.BI
namespace GlobalTheory.BI
theorem _root_.solution {L G V : Type} [Field L] [Group G] [AddCommGroup V]
    [Module L V] (ρ : Representation L G V) (h : ρ.IsIrreducible) : Nontrivial V := by
  by_contra hV
  have : Subsingleton V := not_nontrivial_iff_subsingleton.mp hV
  obtain ⟨x, y, hxy⟩ := h.toNontrivial.exists_pair_ne
  exact hxy (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))
end GlobalTheory.BI
