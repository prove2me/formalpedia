-- Prove2me | solution 1 for GlobalTheory.FrameBasic.mem_perp_span
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:01:38.154247+00:00
-- url     : https://prove2.me/submissions/ceaeb90f-b794-49fa-baff-ed9e5634b26f

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Theorems.Thm_GlobalTheory_FrameBasic_hf_conj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical TensorProduct
open GlobalTheory GlobalTheory.FrameBasic
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.FrameBasic
theorem _root_.solution (L : LocE F E) {n : ℕ} {H : Matrix (Fin n) (Fin n) E} (h : IsHerm L H)
    {ι : Type} (g : ι → Fin n → E) (x : Fin n → E) :
    x ∈ perp L H (Submodule.span E (Set.range g)) ↔ ∀ j, hf L H x (g j) = 0 := by
  refine ⟨fun hx j => hx _ (Submodule.subset_span ⟨j, rfl⟩), fun hx y hy => ?_⟩
  have : Submodule.span E (Set.range g) ≤ LinearMap.ker (hfL L H x) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    change hf L H (g j) x = 0
    rw [hf_conj L h, hx j, map_zero]
  have h2 : hf L H y x = 0 := this hy
  rw [hf_conj L h, h2, map_zero]
end GlobalTheory.FrameBasic
