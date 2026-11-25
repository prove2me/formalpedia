-- Prove2me | solution 1 for GroundTheory.Automorphic.Measures.distribHaarChar_pi_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:28:08.330422+00:00
-- url     : https://prove2.me/submissions/d98ce403-cd10-4b0c-b8a5-ad9456d5eacf

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresModulus
import Theorems.Thm_GroundTheory_Automorphic_Measures_det_glEquiv
import Theorems.Thm_GroundTheory_Automorphic_Measures_distribHaarChar_glEquiv

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
theorem _root_.solution (L : (ι → F) ≃ₗ[F] (ι → F)) :
    distribHaarChar (ι → F) L = distribHaarChar F (LinearEquiv.det L) := by
  obtain ⟨g, rfl⟩ := glEquiv.surjective L
  rw [distribHaarChar_glEquiv, det_glEquiv]
end GroundTheory.Automorphic.Measures
