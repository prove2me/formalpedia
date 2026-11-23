-- Prove2me | solution 1 for GroundTheory.Automorphic.Measures.isOpen_box
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:01:08.746504+00:00
-- url     : https://prove2.me/submissions/6b380bf5-bcf4-4e10-84e9-8337f8101a1b

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresModulus

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
theorem _root_.solution : IsOpen (box F ι) :=
  isOpen_set_pi Set.finite_univ fun _ _ => Valuation.isOpen_integer
end GroundTheory.Automorphic.Measures
