-- Prove2me | solution 1 for GlobalTheory.HL.LevelFamilies.relIndex_eq_card_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:41:13.117261+00:00
-- url     : https://prove2.me/submissions/7b59f648-d99c-4ef5-a72d-16ce523885ce

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardEqPowAndIndexGe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermExponentsNonnegAndDefectGroupBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelIndexEqCardMap
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.LevelFamilies
namespace GlobalTheory.HL.LevelFamilies
theorem _root_.solution {O V : Type} [Ring O] [AddCommGroup V] [Module O V]
    (M A : Submodule O V) :
    M.toAddSubgroup.relIndex A.toAddSubgroup = Nat.card (A.map M.mkQ) := by
  have h := AddSubgroup.relIndex_ker A.toAddSubgroup M.mkQ.toAddMonoidHom
  have hk : M.mkQ.toAddMonoidHom.ker = M.toAddSubgroup := by
    ext x
    simp [AddMonoidHom.mem_ker]
  rw [hk] at h
  rw [h]
  rfl
end GlobalTheory.HL.LevelFamilies
