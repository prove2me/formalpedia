-- Prove2me | solution 1 for GlobalTheory.HL.ThickSplit.mem_fixG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:40:35.99062+00:00
-- url     : https://prove2.me/submissions/21c0dbe3-905d-4c87-8c51-0cf25313f8a5

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
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.HL.ThickSplit
theorem _root_.solution (L : LocE F E) {n m : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
    (x : Fin m → Fin n → E) (g : (Fin n → E) ≃ₗ[E] (Fin n → E)) :
    g ∈ fixG L Hm (Submodule.span E (Set.range x)) ↔ g ∈ isomG L Hm ∧ ∀ a, g (x a) = x a := by
  constructor
  · rintro ⟨h1, _, h3⟩
    refine ⟨h1, fun a => ?_⟩
    have := h3 (x a) (Submodule.subset_span ⟨a, rfl⟩)
    exact sub_eq_zero.1 ((Submodule.mem_bot E).1 this)
  · rintro ⟨h1, h2⟩
    have key : ∀ v ∈ Submodule.span E (Set.range x), g v = v := by
      intro v hv
      induction hv using Submodule.span_induction with
      | mem v hv => obtain ⟨a, rfl⟩ := hv; exact h2 a
      | zero => simp
      | add u v _ _ hu hv => rw [map_add, hu, hv]
      | smul c v _ hv => rw [map_smul, hv]
    refine ⟨h1, fun v => ⟨fun hv => ?_, fun hv => by rw [key v hv]; exact hv⟩, fun v hv => ?_⟩
    · have := g.injective (key _ hv)
      rwa [this] at hv
    · rw [key v hv, sub_self]
      exact Submodule.zero_mem _
end GlobalTheory.HL.ThickSplit
