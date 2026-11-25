-- Prove2me | solution 1 for GlobalTheory.HL.ThickSplit.cont_iUnion_cosets
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:33:52.480141+00:00
-- url     : https://prove2.me/submissions/b5bfc93d-01fa-4e43-a108-7ea16fd001f1

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CommensurableCosetUnionContentBiUnionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TupleJacobianRightMulIsometryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MatrixCongruentOneModUniformizerPowGroupAndOrbitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ContentThickenedTupleOrbitNormalSubgroup
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_T_commensurableCosetUnionContent_biUnion
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.ThickSplit
namespace GlobalTheory.HL.ThickSplit
theorem _root_.solution {W : Type} [AddCommGroup W] (W0 : AddSubgroup W) {Γ : Type} [Group Γ]
    (N H : Subgroup Γ) [N.Normal] (hN : N.index ≠ 0) (S : Γ → Set W) (c : ℝ)
    (hco : ∀ a, IsCO W0 (S a)) (hc : ∀ a, cont W0 (S a) = c)
    (heq : ∀ a b, a⁻¹ * b ∈ N ⊔ H → S a = S b)
    (hdis : ∀ a b, ¬ Disjoint (S a) (S b) → a⁻¹ * b ∈ N ⊔ H) :
    cont W0 (⋃ a, S a) * (N.relIndex H : ℝ) = (N.index : ℝ) * c := by
  have hidx : N.relIndex H * (N ⊔ H).index = N.index := by
    rw [← Subgroup.relIndex_sup_left H N]
    exact Subgroup.relIndex_mul_index le_sup_left
  have hJ : (N ⊔ H).index ≠ 0 := by
    intro h
    rw [h, mul_zero] at hidx
    exact hN hidx.symm
  haveI : (N ⊔ H).FiniteIndex := ⟨hJ⟩
  haveI : Fintype (Γ ⧸ (N ⊔ H)) := Fintype.ofFinite _
  have hU : (⋃ a, S a) = ⋃ q ∈ (Finset.univ : Finset (Γ ⧸ (N ⊔ H))), S q.out := by
    ext w
    simp only [Set.mem_iUnion, Finset.mem_univ, exists_true_left]
    constructor
    · rintro ⟨a, ha⟩
      refine ⟨(a : Γ ⧸ (N ⊔ H)), ?_⟩
      rw [heq _ a (QuotientGroup.eq.1 (QuotientGroup.out_eq' _))]
      exact ha
    · rintro ⟨q, hq⟩
      exact ⟨_, hq⟩
  rw [hU, (GlobalTheory.T.commensurableCosetUnionContent_biUnion W0 Finset.univ (fun q : Γ ⧸ (N ⊔ H) => S q.out) (fun q _ => hco _)).2]
  · simp only [hc, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← hidx, Subgroup.index, Nat.card_eq_fintype_card]
    push_cast
    ring
  · intro q _ r _ hqr
    by_contra h
    apply hqr
    have := QuotientGroup.eq.2 (hdis _ _ h)
    rwa [QuotientGroup.out_eq', QuotientGroup.out_eq'] at this
end GlobalTheory.HL.ThickSplit
