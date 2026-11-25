-- Prove2me | solution 1 for GlobalTheory.T.eichlerLattice_locally_constant_data
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:43:21.359453+00:00
-- url     : https://prove2.me/submissions/615c0ee3-b945-4c08-bf57-35d98898c7ba

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerLatticeLocallyConstantData
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_Cint
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NoLeak
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerLatticeLocallyConstantDataStatement
import Theorems.Thm_GlobalTheory_HL_EichlerLocal_moved_locally_constant


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ Λ : Submodule L.O S.V, IsSD L S.Hm Λ → ∀ c : ℕ, ∃ N : ℕ, ∀ (x x₁ u u₁ : S.V) (s s₁ : E), S.h x x = 0 → S.h u x = 0 → s + L.cj s = S.h u u → S.h x₁ x₁ = 0 → S.h u₁ x₁ = 0 → s₁ + L.cj s₁ = S.h u₁ u₁ → algebraMap F E ((S.ϖ : F) ^ c) • x ∈ Λ → u ∈ Λ → s ∈ L.O → (∃ y ∈ Λ, x₁ - x = algebraMap F E ((S.ϖ : F) ^ N) • y) → (∃ y ∈ Λ, u₁ - u = algebraMap F E ((S.ϖ : F) ^ N) • y) → (∃ y ∈ L.O, s₁ - s = algebraMap F E ((S.ϖ : F) ^ N) * y) → S.moved Λ x₁ u₁ s₁ = S.moved Λ x u s := by
  first | exact @GlobalTheory.HL.EichlerLocal.moved_locally_constant | exact GlobalTheory.HL.EichlerLocal.moved_locally_constant | (intros; apply GlobalTheory.HL.EichlerLocal.moved_locally_constant <;> assumption)
end _root_.GlobalTheory.T
