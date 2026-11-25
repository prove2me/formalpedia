-- Prove2me | solution 1 for GlobalTheory.HL.FibU.exists_reps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:33:53.050262+00:00
-- url     : https://prove2.me/submissions/47eafac2-21f5-4fca-b4da-45e927f8c396

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_Cint
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NoLeak
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_QuadricCharacterLeakSharesFiniteStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IndexMeasureIntegralEqMeanOverRepresentativesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsPowSmulMemOfIsLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermIntegralNearOneBound
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
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.FibU
namespace GlobalTheory.HL.FibU
theorem _root_.solution {W : Type} [AddCommGroup W] (A P : AddSubgroup W) (h : P.relIndex A ≠ 0) :
    ∃ R : Finset W, (∀ w ∈ R, w ∈ A) ∧ ∀ w ∈ A, ∃! x, x ∈ R ∧ w - x ∈ P := by
  have hf : Finite (A ⧸ P.addSubgroupOf A) := Nat.finite_of_card_ne_zero h
  have := Fintype.ofFinite (A ⧸ P.addSubgroupOf A)
  refine ⟨Finset.univ.image fun c : A ⧸ P.addSubgroupOf A => ((c.out : A) : W), ?_, ?_⟩
  · intro w hw
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hw
    exact c.out.2
  · intro w hw
    have key : ∀ c : A ⧸ P.addSubgroupOf A, w - ((c.out : A) : W) ∈ P ↔
        c = QuotientAddGroup.mk (⟨w, hw⟩ : A) := by
      intro c
      conv_rhs => rw [← QuotientAddGroup.out_eq' c]
      rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
      simp [neg_add_eq_sub]
    refine ⟨_, ⟨Finset.mem_image.2 ⟨QuotientAddGroup.mk (⟨w, hw⟩ : A), Finset.mem_univ _, rfl⟩,
      (key _).2 rfl⟩, ?_⟩
    rintro x ⟨hx, hx'⟩
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hx
    rw [(key c).1 hx']
end GlobalTheory.HL.FibU
