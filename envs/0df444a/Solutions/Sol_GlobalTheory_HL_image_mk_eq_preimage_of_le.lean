-- Prove2me | solution 1 for GlobalTheory.HL.image_mk_eq_preimage_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:32:31.172922+00:00
-- url     : https://prove2.me/submissions/983db14c-3db8-4735-b296-759515082b53

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CommensurableCosetUnionContentIndependentNonneg
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
open GlobalTheory GlobalTheory.HL
namespace GlobalTheory.HL
theorem _root_.solution {W : Type} [AddCommGroup W] {A A' : AddSubgroup W} {S : Set W}
    (hle : A' ≤ A) (hS : ∀ x ∈ S, ∀ a ∈ A, x + a ∈ S) :
    (QuotientAddGroup.mk : W → W ⧸ A') '' S =
      (AddSubgroup.quotientEquivProdOfLE hle) ⁻¹'
        (((QuotientAddGroup.mk : W → W ⧸ A) '' S) ×ˢ Set.univ) := by
  ext q
  induction q using QuotientAddGroup.induction_on with
  | H x =>
    have h1 : (AddSubgroup.quotientEquivProdOfLE hle (QuotientAddGroup.mk x)).1 =
        (QuotientAddGroup.mk x : W ⧸ A) := rfl
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, and_true, h1]
    constructor
    · rintro ⟨y, hy, hyx⟩
      exact ⟨y, hy, QuotientAddGroup.eq.2 (hle (QuotientAddGroup.eq.1 hyx))⟩
    · rintro ⟨y, hy, hyx⟩
      have := hS y hy _ (QuotientAddGroup.eq.1 hyx)
      refine ⟨x, ?_, rfl⟩
      simpa using this
end GlobalTheory.HL
