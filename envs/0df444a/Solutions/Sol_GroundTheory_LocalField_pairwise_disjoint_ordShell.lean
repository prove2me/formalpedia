-- Prove2me | solution 1 for GroundTheory.LocalField.pairwise_disjoint_ordShell
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:40:58.169253+00:00
-- url     : https://prove2.me/submissions/96d3a33a-2fc9-434d-863f-510a15b8e256

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalFourier
import Definitions.Def_GroundTheory_LocalFields_LocalZetaShell

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel MeasureTheory Measure Topology Filter
open scoped WithZero NNReal ENNReal Pointwise
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
namespace GroundTheory.LocalField
theorem _root_.solution : Pairwise (Function.onFun Disjoint (ordShell K)) := by
  intro i j hij
  exact Set.disjoint_left.mpr fun u hi hj => hij (hi.symm.trans hj)
end GroundTheory.LocalField
