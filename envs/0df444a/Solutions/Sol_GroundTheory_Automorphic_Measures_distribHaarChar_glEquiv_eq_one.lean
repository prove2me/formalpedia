-- Prove2me | solution 1 for GroundTheory.Automorphic.Measures.distribHaarChar_glEquiv_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:05:54.705271+00:00
-- url     : https://prove2.me/submissions/7e3224ba-de40-4975-b38a-589d7f8a818c

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresModulus
import Theorems.Thm_GroundTheory_Automorphic_Measures_distribHaarChar_eq_one_of_mapsTo_box
import Theorems.Thm_GroundTheory_Automorphic_Measures_mulVec_mem_box
import Theorems.Thm_GroundTheory_Automorphic_Measures_glEquiv_apply

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
variable [DecidableEq ι]
namespace GroundTheory.Automorphic.Measures
theorem _root_.solution {g : GL ι F} (h₁ : ∀ a b, (g : Matrix ι ι F) a b ∈ 𝒪[F])
    (h₂ : ∀ a b, ((g⁻¹ : GL ι F) : Matrix ι ι F) a b ∈ 𝒪[F]) :
    distribHaarChar (ι → F) (glEquiv g) = 1 := by
  refine distribHaarChar_eq_one_of_mapsTo_box (fun x hx => ?_) (fun x hx => ?_)
  · rw [glEquiv_apply]
    exact mulVec_mem_box h₁ hx
  · rw [show (glEquiv g).symm = glEquiv g⁻¹ from (map_inv glEquiv g).symm, glEquiv_apply]
    exact mulVec_mem_box h₂ hx
end GroundTheory.Automorphic.Measures
