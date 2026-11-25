-- Prove2me | solution 1 for GroundTheory.LocalField.unifUnit_zpow_neg_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:53:14.411887+00:00
-- url     : https://prove2.me/submissions/b2017e54-a09a-4f15-8468-ceebe368edc9

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZetaShell
import Definitions.Def_GroundTheory_LocalFields_LocalZetaChar

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
theorem _root_.solution (u : Kˣ) :
    unifUnit K ^ (-ord (u : K)) * u ∈ unitFiltrationUnits K 0 := by
  rw [mem_unitFiltrationUnits_zero_iff_ord, ord_units_mul, ord_unifUnit_zpow]
  ring
end GroundTheory.LocalField
