-- Prove2me | solution 1 for GroundTheory.Automorphic.Measures.glEquiv_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:01:56.300809+00:00
-- url     : https://prove2.me/submissions/63530a21-35a3-4a1c-9627-048a58432b1b

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
variable [DecidableEq ι]
namespace GroundTheory.Automorphic.Measures
theorem _root_.solution (g : GL ι F) (x : ι → F) : glEquiv g x = (g : Matrix ι ι F).mulVec x := by
  simp [glEquiv, LinearMap.GeneralLinearGroup.generalLinearEquiv, Matrix.GeneralLinearGroup.toLin]
end GroundTheory.Automorphic.Measures
