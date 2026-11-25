-- Prove2me | solution 1 for GlobalTheory.HL.DivisibleGauss.card_reps_eq_relIndex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:34:55.22486+00:00
-- url     : https://prove2.me/submissions/78593cb6-bd52-4f51-9d42-7af4a17652e7

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SqNormSumRepsMulIndexLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianLocalCharacterSum
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
open scoped Pointwise ENNReal Classical ComplexConjugate
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.DivisibleGauss
namespace GlobalTheory.HL.DivisibleGauss
theorem _root_.solution {V : Type*} [AddCommGroup V] (M P : AddSubgroup V) (R : Finset V)
    (hRM : ∀ u ∈ R, u ∈ M) (hR : ∀ u ∈ M, ∃! w, w ∈ R ∧ u - w ∈ P) :
    R.card = P.relIndex M := by
  have hb : Function.Bijective fun w : R =>
      (QuotientAddGroup.mk (⟨w, hRM w w.2⟩ : M) : M ⧸ P.addSubgroupOf M) := by
    constructor
    · intro w w' h
      have h' := QuotientAddGroup.eq_iff_sub_mem.1 h
      exact Subtype.ext ((hR w (hRM w w.2)).unique ⟨w.2, by simp⟩ ⟨w'.2, h'⟩)
    · intro x
      obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective x
      obtain ⟨w, ⟨hw, hw'⟩, -⟩ := hR u u.2
      exact ⟨⟨w, hw⟩, (QuotientAddGroup.eq_iff_sub_mem.2
        (show u - ⟨w, hRM w hw⟩ ∈ P.addSubgroupOf M from hw')).symm⟩
  rw [← Fintype.card_coe, ← Nat.card_eq_fintype_card]
  exact Nat.card_eq_of_bijective _ hb
end GlobalTheory.HL.DivisibleGauss
