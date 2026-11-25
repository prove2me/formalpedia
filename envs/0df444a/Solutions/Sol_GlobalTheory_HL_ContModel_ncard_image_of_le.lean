-- Prove2me | solution 1 for GlobalTheory.HL.ContModel.ncard_image_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:45:49.391354+00:00
-- url     : https://prove2.me/submissions/280c946b-520e-408c-84b7-d0c225280a84

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NcardImageOfLe
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
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.ContModel
namespace GlobalTheory.HL.ContModel
theorem _root_.solution {W : Type} [AddCommGroup W] {A B : AddSubgroup W} (h : B ≤ A) (S : Set W)
    (hS : ∀ x ∈ S, ∀ a ∈ A, x + a ∈ S) :
    ((QuotientAddGroup.mk : W → W ⧸ B) '' S).ncard
      = ((QuotientAddGroup.mk : W → W ⧸ A) '' S).ncard * B.relIndex A := by
  have e := AddSubgroup.quotientEquivProdOfLE h
  have key : (AddSubgroup.quotientEquivProdOfLE h) '' ((QuotientAddGroup.mk : W → W ⧸ B) '' S)
      = ((QuotientAddGroup.mk : W → W ⧸ A) '' S) ×ˢ Set.univ := by
    ext ⟨u, v⟩
    simp only [Set.mem_prod, Set.mem_univ, and_true]
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, hxy⟩
      refine ⟨x, hx, ?_⟩
      have := congrArg Prod.fst hxy
      exact this
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨z, hz⟩ := (AddSubgroup.quotientEquivProdOfLE h).surjective
        ((QuotientAddGroup.mk x : W ⧸ A), v)
      obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective z
      refine ⟨_, ⟨y, ?_, rfl⟩, hz⟩
      have h1 : (QuotientAddGroup.mk y : W ⧸ A) = QuotientAddGroup.mk x := congrArg Prod.fst hz
      have h2 := QuotientAddGroup.eq.1 h1.symm
      have := hS x hx _ h2
      simpa using this
  rw [← Set.ncard_image_of_injective _ (AddSubgroup.quotientEquivProdOfLE h).injective, key,
    Set.ncard_prod, Set.ncard_univ]
  rfl
end GlobalTheory.HL.ContModel
