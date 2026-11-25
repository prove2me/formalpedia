-- Prove2me | solution 1 for GroundTheory.Automorphic.Measures.distribHaarChar_eq_one_of_mapsTo_box
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:00:45.170834+00:00
-- url     : https://prove2.me/submissions/96d6a1b8-f64d-4651-bd40-98392a348959

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresModulus
import Theorems.Thm_GroundTheory_Automorphic_Measures_distribHaarChar_eq_one_of_image_box

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Measure Topology Filter Set ValuativeRel
open scoped NNReal ENNReal Pointwise
set_option linter.unusedSectionVars false
open GroundTheory.Automorphic.Measures
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {F} {ι : Type*} [Fintype ι]
namespace GroundTheory.Automorphic.Measures
theorem _root_.solution {L : (ι → F) ≃ₗ[F] (ι → F)}
    (h₁ : ∀ x ∈ box F ι, L x ∈ box F ι) (h₂ : ∀ x ∈ box F ι, L.symm x ∈ box F ι) :
    distribHaarChar (ι → F) L = 1 := by
  refine distribHaarChar_eq_one_of_image_box (Set.Subset.antisymm ?_ fun x hx => ?_)
  · rintro _ ⟨x, hx, rfl⟩
    exact h₁ x hx
  · exact ⟨L.symm x, h₂ x hx, L.apply_symm_apply x⟩
end GroundTheory.Automorphic.Measures
