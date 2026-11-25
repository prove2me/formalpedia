-- Prove2me | solution 1 for GlobalTheory.HL.FrameTuple.tup_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:34:10.959911+00:00
-- url     : https://prove2.me/submissions/0a1bc7d2-9889-4213-ad91-206a817d2342

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsNondegenerateTupleComplementFixer
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
noncomputable section
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.FrameTuple
variable {E V : Type} [CommRing E] [AddCommGroup V] [Module E V] {m : ℕ}
namespace GlobalTheory.HL.FrameTuple
theorem _root_.solution {t θ : E} (h : θ * t = 1) (g g' : Fin m → V) :
    Submodule.span E (Set.range (tup t g g')) = Submodule.span E (Set.range (Sum.elim g g')) := by
  apply le_antisymm <;> rw [Submodule.span_le]
  · rintro _ ⟨a | b, rfl⟩
    · exact Submodule.subset_span ⟨Sum.inl a, rfl⟩
    · exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.subset_span ⟨Sum.inr b, rfl⟩)
        (Submodule.subset_span ⟨Sum.inl b, rfl⟩))
  · rintro _ ⟨a | b, rfl⟩
    · exact Submodule.subset_span ⟨Sum.inl a, rfl⟩
    · have : Sum.elim g g' (Sum.inr b) = tup t g g' (Sum.inl b) + θ • tup t g g' (Sum.inr b) := by
        simp [tup, smul_smul, h]
      rw [this]
      exact Submodule.add_mem _ (Submodule.subset_span ⟨Sum.inl b, rfl⟩)
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr b, rfl⟩))
end GlobalTheory.HL.FrameTuple
