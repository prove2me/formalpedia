-- Prove2me | solution 1 for GlobalTheory.HL.Defect.index_le_of_chars
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:35:08.565493+00:00
-- url     : https://prove2.me/submissions/1a207a82-d4af-47cd-ac80-d48f4ef56a8e

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardEqPowAndIndexGe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemPerpSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DetUpdateRowLastSingle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardCokernelUnramifiedOrderMatrixOfDetBaseStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetFramesLevelLeIffCongrFlagSteStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermExponentsNonnegAndDefectGroupBound
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.Defect
open GlobalTheory.HL.Eichler GlobalTheory.HL.StdLat GlobalTheory.UnramOrder Matrix
namespace GlobalTheory.HL.Defect
theorem _root_.solution {N P : Type} [AddCommGroup N] [AddCommGroup P] (M : AddSubgroup N)
    (Q : AddSubgroup P) (hQ : Q.index ≠ 0) (χ : N → AddChar P ℂ) (h1 : ∀ y, ∀ p ∈ Q, χ y p = 1)
    (h2 : ∀ y y', χ y = χ y' → y - y' ∈ M) : M.index ≤ Q.index := by
  have : Finite (P ⧸ Q) := Nat.finite_of_card_ne_zero hQ
  let := Fintype.ofFinite (P ⧸ Q)
  let f : N ⧸ M → AddChar (P ⧸ Q) ℂ := fun x =>
    { toFun := fun t => χ x.out t.out
      map_zero_eq_one' := h1 _ _ (by
        rw [← QuotientAddGroup.eq_zero_iff, QuotientAddGroup.out_eq'])
      map_add_eq_mul' := fun a b => by
        have h : (a + b).out - (a.out + b.out) ∈ Q := by
          rw [← QuotientAddGroup.eq_iff_sub_mem]; simp
        have := h1 x.out _ h
        rw [← AddChar.map_add_eq_mul, ← sub_add_cancel (a + b).out (a.out + b.out),
          AddChar.map_add_eq_mul, this, one_mul] }
  have hf : ∀ x (p : P), f x (p : P ⧸ Q) = χ x.out p := fun x p => by
    have h : (p : P ⧸ Q).out - p ∈ Q := by
      rw [← QuotientAddGroup.eq_iff_sub_mem]; simp
    change χ x.out (p : P ⧸ Q).out = _
    rw [← sub_add_cancel (p : P ⧸ Q).out p, AddChar.map_add_eq_mul, h1 _ _ h, one_mul]
  have hinj : Function.Injective f := fun x x' h => by
    have : χ x.out = χ x'.out := by
      ext p; rw [← hf, ← hf, h]
    have h3 := QuotientAddGroup.eq_iff_sub_mem.2 (h2 _ _ this)
    simpa using h3
  calc M.index ≤ Nat.card (AddChar (P ⧸ Q) ℂ) := Nat.card_le_card_of_injective f hinj
    _ ≤ Q.index := by
      rw [AddSubgroup.index, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
      exact AddChar.card_addChar_le _ _
end GlobalTheory.HL.Defect
