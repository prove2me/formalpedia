-- Prove2me | solution 1 for GlobalTheory.SgLoc.isField_or_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:13:44.373497+00:00
-- url     : https://prove2.me/submissions/27242e9a-5f0c-408c-b4bc-7c0ecac4dd6e

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_RowRawRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralValIntegerIff
import Theorems.Thm_GlobalTheory_SgLoc_LocE_isField_or_split
import Theorems.Thm_GlobalTheory_SgLoc_isIntegral_valInteger_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel MeasureTheory ComplexConjugate Formalism.MainNotions.S.Loc GlobalTheory.SgLoc
open scoped ComplexOrder
open GlobalTheory GlobalTheory.SgLoc
namespace GlobalTheory.SgLoc
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → IsField E ∨ ∃ e : E ≃ₐ[F] F × F, (∀ x, e (M.L.cj x) = (e x).swap) ∧ Continuous e ∧ Continuous e.symm ∧ ∀ x, x ∈ M.L.O ↔ ((e x).1 ∈ 𝒪[F] ∧ (e x).2 ∈ 𝒪[F]) := by
  intro F _ _ _ E _ _ _ _ M hM
  rcases LocE_isField_or_split M.L with h | ⟨e, he⟩
  · exact Or.inl h
  haveI := hM.loc
  haveI := M.L.top
  haveI : ContinuousAdd E := IsModuleTopology.toContinuousAdd F E
  refine Or.inr ⟨e, he, ?_, ?_, fun x => ?_⟩
  · exact IsModuleTopology.continuous_of_linearMap e.toLinearMap
  · exact IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  · rw [M.L.O_def, ← isIntegral_algEquiv (e.restrictScalars 𝒪[F]), ← isIntegral_valInteger_iff,
      ← isIntegral_valInteger_iff, ← IsIntegral.pair_iff]
    rfl
end GlobalTheory.SgLoc
