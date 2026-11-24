-- Prove2me | solution 1 for GlobalTheory.T.exists_int_relation_of_isIntegral_relation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:08:07.495836+00:00
-- url     : https://prove2.me/submissions/f4ed2189-7924-442a-b3d7-c83d4d9d20ac

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsIntRelationOfIsIntegralRelation
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsIntRelationOfIsIntegralRelationStatement
import Theorems.Thm_GlobalTheory_CuspGL_exists_int_retraction_of_isIntegral


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
theorem _root_.solution : ∀ (ι : Type) [Fintype ι] (r : ι → ℂ), (∀ i, IsIntegral ℤ (r i)) → ∃ c : ι → ℤ, ∀ (m : ι → ℤ) (d : ℤ), ∑ i, r i * (m i : ℂ) = d → ∑ i, c i * m i = d := by
  first | exact @GlobalTheory.CuspGL.exists_int_retraction_of_isIntegral | exact GlobalTheory.CuspGL.exists_int_retraction_of_isIntegral | (intros; apply GlobalTheory.CuspGL.exists_int_retraction_of_isIntegral <;> assumption)
end _root_.GlobalTheory.T
