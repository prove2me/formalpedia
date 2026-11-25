-- Prove2me | solution 1 for GlobalTheory.HL.ContAut.image_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:33:47.672022+00:00
-- url     : https://prove2.me/submissions/cdbde98c-3a55-4d07-9187-ec1bba54e956

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NcardImageOfLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelVolMul
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.ContAut
namespace GlobalTheory.HL.ContAut
theorem _root_.solution {W : Type} [AddCommGroup W] (A : AddSubgroup W) (φ : W ≃+ W) (S : Set W) :
    ∃ f : W ⧸ A → W ⧸ A.map φ.toAddMonoidHom, Function.Injective f ∧
      (QuotientAddGroup.mk : W → W ⧸ A.map φ.toAddMonoidHom) '' (φ '' S)
        = f '' ((QuotientAddGroup.mk : W → W ⧸ A) '' S) := by
  refine ⟨QuotientAddGroup.map A (A.map φ.toAddMonoidHom) φ.toAddMonoidHom
    (AddSubgroup.le_comap_map _ _), ?_, ?_⟩
  · intro u v
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective u
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective v
    intro h
    rw [QuotientAddGroup.map_mk, QuotientAddGroup.map_mk, QuotientAddGroup.eq] at h
    obtain ⟨a, ha, hh⟩ := h
    rw [QuotientAddGroup.eq]
    have : a = -x + y := φ.injective (by simpa using hh)
    rwa [← this]
  · rw [Set.image_image, Set.image_image]
    rfl
end GlobalTheory.HL.ContAut
