-- Prove2me | solution 1 for GlobalTheory.HL.QReflGen.exists_skew
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:41:02.197048+00:00
-- url     : https://prove2.me/submissions/142e03f6-e32f-4b08-8a02-b6f493fe2f15

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeOfPerpEqBot
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsometriesFixingSubspaceLeQuasiReflectionClosure
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
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.QReflGen
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.HL.QReflGen
theorem _root_.solution (L : LocE F E) :
    ∃ (δ : E) (D : F), D ≠ 0 ∧ L.cj δ = -δ ∧ δ * δ = algebraMap F E D := by
  have h1 : ∃ z : E, L.cj z ≠ z := by
    by_contra h
    push_neg at h
    have hs : Function.Surjective (Algebra.linearMap F E) := fun z => (L.cj_fix z).1 (h z)
    have := LinearMap.finrank_le_finrank_of_surjective hs
    rw [L.rank, Module.finrank_self] at this
    omega
  obtain ⟨z, hz⟩ := h1
  have hδ : L.cj (z - L.cj z) = -(z - L.cj z) := by simp [L.cj_cj]
  obtain ⟨D, hD⟩ := (L.cj_fix ((z - L.cj z) * (z - L.cj z))).1 (by rw [map_mul, hδ]; ring)
  refine ⟨z - L.cj z, D, ?_, hδ, hD.symm⟩
  rintro rfl
  haveI := L.reduced
  have : z - L.cj z = 0 := IsNilpotent.eq_zero ⟨2, by rw [pow_two, ← hD]; simp⟩
  exact hz (sub_eq_zero.1 this).symm
end GlobalTheory.HL.QReflGen
