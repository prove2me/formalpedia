-- Prove2me | solution 1 for GlobalTheory.HL.OffLeak.relIndex_eq_of_reps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:43:15.502825+00:00
-- url     : https://prove2.me/submissions/7001123b-d049-4740-b05f-68eb4bb7a8c7

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

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.OffLeak
namespace GlobalTheory.HL.OffLeak
theorem _root_.solution {R V : Type*} [Ring R] [AddCommGroup V] [Module R V] (M T B : Submodule R V)
    (hM : M ≤ T) (hB : B ≤ T) (h : ∀ y ∈ T, ∃ y₀ ∈ B, y - y₀ ∈ M) :
    M.toAddSubgroup.relIndex T.toAddSubgroup =
      (M.toAddSubgroup ⊓ B.toAddSubgroup).relIndex B.toAddSubgroup := by
  have hT : T.toAddSubgroup = B.toAddSubgroup ⊔ M.toAddSubgroup := by
    apply le_antisymm
    · intro y hy
      obtain ⟨y₀, hy₀, hm⟩ := h y hy
      have hs : y₀ + (y - y₀) ∈ B.toAddSubgroup ⊔ M.toAddSubgroup :=
        AddSubgroup.add_mem_sup hy₀ hm
      have e : y₀ + (y - y₀) = y := by abel
      rw [e] at hs
      exact hs
    · exact sup_le (fun x hx => hB hx) (fun x hx => hM hx)
  rw [hT, AddSubgroup.relIndex_sup_right, AddSubgroup.inf_relIndex_right]
end GlobalTheory.HL.OffLeak
