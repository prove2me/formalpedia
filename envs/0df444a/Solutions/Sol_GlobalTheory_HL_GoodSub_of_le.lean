-- Prove2me | solution 1 for GlobalTheory.HL.GoodSub.of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:39:59.136291+00:00
-- url     : https://prove2.me/submissions/a8baca8b-56d1-412f-ab09-1fdc868b1915

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CommensurableCosetUnionContentIndependentNonneg
import Theorems.Thm_GlobalTheory_HL_image_mk_eq_preimage_of_le

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
open GlobalTheory GlobalTheory.HL
namespace GlobalTheory.HL
namespace GoodSub
theorem _root_.solution {W : Type} [AddCommGroup W] {W0 A A' : AddSubgroup W} {S : Set W}
    (h : GoodSub W0 A S) (hle : A' ≤ A) (hi : A'.relIndex A ≠ 0) : GoodSub W0 A' S := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨AddSubgroup.relIndex_ne_zero_trans hi h1,
    fun h0 => h2 (AddSubgroup.relIndex_eq_zero_of_le_right hle h0),
    fun x hx a ha => h3 x hx a (hle ha), ?_⟩
  rw [image_mk_eq_preimage_of_le hle h3]
  haveI : Finite (A ⧸ A'.addSubgroupOf A) := Nat.finite_of_card_ne_zero hi
  exact (h4.prod Set.finite_univ).preimage (Equiv.injective _).injOn
end GoodSub
end GlobalTheory.HL
