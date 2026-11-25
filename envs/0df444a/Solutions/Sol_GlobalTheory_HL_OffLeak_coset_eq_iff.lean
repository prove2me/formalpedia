-- Prove2me | solution 1 for GlobalTheory.HL.OffLeak.coset_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:31:53.947972+00:00
-- url     : https://prove2.me/submissions/8793421f-3a71-477b-9997-2c3557afda89

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermLevelZeroAndBoundedRepresentativesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianMovePreservesFrameLatticeLevelsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDefectClassMemTraceFirstFrameSpanStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PairingSecondTypeTestOnRepresentativesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetInFamilyMovedOfNotLeak
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_TermBasic_sub_mem
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.OffLeak
namespace GlobalTheory.HL.OffLeak
theorem _root_.solution {R V : Type*} [Ring R] [AddCommGroup V] [Module R V] (M : Submodule R V) (a b : V) :
    ({x | x - a ∈ M} : Set V) = {x | x - b ∈ M} ↔ a - b ∈ M := by
  constructor
  · intro h
    have ha : a ∈ ({x | x - a ∈ M} : Set V) := by simp
    rw [h] at ha
    exact ha
  · intro h
    ext x
    constructor
    · intro hx
      have hxb : (x - a) + (a - b) ∈ M := M.add_mem hx h
      have e : (x - a) + (a - b) = x - b := by abel
      rw [e] at hxb
      exact hxb
    · intro hx
      have hxa : (x - b) - (a - b) ∈ M := M.sub_mem hx h
      have e : (x - b) - (a - b) = x - a := by abel
      rw [e] at hxa
      exact hxa
end GlobalTheory.HL.OffLeak
