-- Prove2me | solution 1 for GroundTheory.LocalField.summable_of_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:12:43.006683+00:00
-- url     : https://prove2.me/submissions/c044b604-dc27-48a8-99e4-ba810ab79269

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeAndRangePowLe
import Definitions.Def_GroundTheory_LocalFields_ExamplesCharZero
import Definitions.Def_GroundTheory_LocalFields_PadicLogSeries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField
open ValuativeRel IsLocalRing Topology Filter
open scoped WithZero
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
namespace GroundTheory.LocalField
theorem _root_.solution {f : ℕ → K} (hf : Tendsto f atTop (𝓝 0)) : Summable f := by
  let := IsTopologicalAddGroup.rightUniformSpace K
  have := isUniformAddGroup_of_addCommGroup (G := K)
  exact NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero (by rwa [Nat.cofinite_eq_atTop])
end GroundTheory.LocalField
