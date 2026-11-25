-- Prove2me | solution 1 for GroundTheory.Automorphic.Measures.det_glEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:55:24.339252+00:00
-- url     : https://prove2.me/submissions/d3bb089d-ad53-4499-b514-eff9a531694c

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
theorem _root_.solution (g : GL ι F) :
    LinearEquiv.det (glEquiv g) = Matrix.GeneralLinearGroup.det g := by
  ext
  rw [LinearEquiv.coe_det]
  show LinearMap.det (Matrix.toLin' (g : Matrix ι ι F)) = _
  rw [LinearMap.det_toLin']
  rfl
end GroundTheory.Automorphic.Measures
