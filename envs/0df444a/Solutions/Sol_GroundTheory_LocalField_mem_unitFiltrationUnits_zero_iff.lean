-- Prove2me | solution 1 for GroundTheory.LocalField.mem_unitFiltrationUnits_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:34:13.235384+00:00
-- url     : https://prove2.me/submissions/5c60c793-d4a0-458e-8581-64cad3c04692

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeAndRangePowLe
import Theorems.Thm_GroundTheory_LocalField_mem_range_unitsIncl_iff


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
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {K}
namespace GroundTheory.LocalField
theorem _root_.solution {x : Kˣ} :
    x ∈ unitFiltrationUnits K 0 ↔ valuation K (x : K) = 1 := by
  rw [unitFiltrationUnits, unitFiltration_zero, ← MonoidHom.range_eq_map, mem_range_unitsIncl_iff,
    ← map_one (normalizedValuation K), normalizedValuation_eq_iff, map_one]
end GroundTheory.LocalField
