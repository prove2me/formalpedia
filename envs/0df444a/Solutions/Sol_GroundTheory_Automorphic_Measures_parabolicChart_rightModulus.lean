-- Prove2me | solution 1 for GroundTheory.Automorphic.Measures.parabolicChart_rightModulus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:06:50.541416+00:00
-- url     : https://prove2.me/submissions/19eff4fd-22b8-475f-99f7-47a5934c09fd

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresGL
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresParabolic
import Theorems.Thm_GroundTheory_Automorphic_Measures_distribHaarChar_pi_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Measure Topology Filter Set ValuativeRel Iwasawa
open scoped NNReal ENNReal Pointwise
set_option linter.unusedSectionVars false
open GroundTheory.Automorphic.Measures
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (n : ℕ) {α : Type*} [LinearOrder α] (β : Fin n → α)
variable {F n β}
namespace GroundTheory.Automorphic.Measures
theorem _root_.solution (p : blockUpper F n β) :
    (parabolicChart F n β).rightModulus p =
      distribHaarChar F (LinearEquiv.det (mulRightLie F n β p)) := by
  rw [LinearChart.rightModulus, distribHaarChar_pi_eq]
  congr 1
  exact LinearEquiv.det_conj (mulRightLie F n β p) (parabolicCoord F n β)
end GroundTheory.Automorphic.Measures
