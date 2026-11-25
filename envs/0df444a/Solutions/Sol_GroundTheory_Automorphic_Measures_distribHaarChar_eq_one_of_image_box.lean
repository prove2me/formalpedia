-- Prove2me | solution 1 for GroundTheory.Automorphic.Measures.distribHaarChar_eq_one_of_image_box
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:55:25.526436+00:00
-- url     : https://prove2.me/submissions/22e65f01-d909-4022-b110-de2c3cbd3a7d

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresModulus
import Theorems.Thm_GroundTheory_Automorphic_Measures_isOpen_box
import Theorems.Thm_GroundTheory_Automorphic_Measures_isCompact_box
import Theorems.Thm_GroundTheory_Automorphic_Measures_zero_mem_box

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
    (h : L '' box F ι = box F ι) : distribHaarChar (ι → F) L = 1 := by
  borelize (ι → F)
  let μ : Measure (ι → F) := Measure.addHaar
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ) (s := box F ι)
    (isOpen_box.measure_ne_zero μ ⟨0, zero_mem_box⟩) isCompact_box.measure_lt_top.ne ?_
  have : L • box F ι = L '' box F ι := rfl
  rw [this, h, ENNReal.coe_one, one_mul]
end GroundTheory.Automorphic.Measures
