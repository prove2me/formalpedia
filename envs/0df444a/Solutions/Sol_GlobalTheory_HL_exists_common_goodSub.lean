-- Prove2me | solution 1 for GlobalTheory.HL.exists_common_goodSub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:53:55.671148+00:00
-- url     : https://prove2.me/submissions/c47bac83-855a-4da1-a7e9-0fe1575a30d9

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CommensurableCosetUnionContentIndependentNonnegStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CommensurableCosetUnionContentBiUnion
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_T_commensurableCosetUnionContent_independent_nonneg
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
open GlobalTheory GlobalTheory.HL
namespace GlobalTheory.HL
theorem _root_.solution {W : Type} [AddCommGroup W] (W0 : AddSubgroup W) {ι : Type}
    (s : Finset ι) (S : ι → Set W) (h : ∀ i ∈ s, IsCO W0 (S i)) :
    ∃ A, GoodSub W0 A ∅ ∧ ∀ i ∈ s, GoodSub W0 A (S i) := by
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨W0, ⟨by simp, by simp, by simp, by simp⟩, by simp⟩
  | insert j s hj ih =>
    obtain ⟨A, hA0, hA⟩ := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    obtain ⟨B, hB⟩ := h j (Finset.mem_insert_self _ _)
    have h1 : (A ⊓ B).relIndex A ≠ 0 := by
      rw [AddSubgroup.inf_relIndex_left]
      exact AddSubgroup.relIndex_ne_zero_trans hB.1 hA0.2.1
    have h2 : (A ⊓ B).relIndex B ≠ 0 := by
      rw [AddSubgroup.inf_relIndex_right]
      exact AddSubgroup.relIndex_ne_zero_trans hA0.1 hB.2.1
    refine ⟨A ⊓ B, (GlobalTheory.T.commensurableCosetUnionContent_independent_nonneg W0 ∅).2.1 A _ hA0 inf_le_left h1, fun i hi => ?_⟩
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact (GlobalTheory.T.commensurableCosetUnionContent_independent_nonneg W0 _).2.1 B _ hB inf_le_right h2
    · exact (GlobalTheory.T.commensurableCosetUnionContent_independent_nonneg W0 _).2.1 A _ (hA i hi) inf_le_left h1
end GlobalTheory.HL
