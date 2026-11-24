-- Prove2me | solution 1 for GlobalTheory.T.exists_teichmuller_map_algebraicClosure_finiteField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:08:05.727818+00:00
-- url     : https://prove2.me/submissions/e9dc9c22-0dc3-47a9-92de-e325d5b55689

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsTeichmullerMapAlgebraicClosureFiniteField
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsTeichmullerMapAlgebraicClosureFiniteFieldStatement
import Theorems.Thm_GlobalTheory_CuspGL_TeichEmb_exists_teichmuller


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [Field F] [Finite F], ∃ θ : AlgebraicClosure F →* ℂ, ∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y := by
  first | exact @GlobalTheory.CuspGL.TeichEmb.exists_teichmuller | exact GlobalTheory.CuspGL.TeichEmb.exists_teichmuller | (intros; apply GlobalTheory.CuspGL.TeichEmb.exists_teichmuller <;> assumption)
end _root_.GlobalTheory.T
