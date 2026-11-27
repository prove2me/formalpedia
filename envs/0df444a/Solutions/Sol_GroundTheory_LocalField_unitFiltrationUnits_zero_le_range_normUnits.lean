-- Prove2me | solution 1 for GroundTheory.LocalField.unitFiltrationUnits_zero_le_range_normUnits
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:52:59.138997+00:00
-- url     : https://prove2.me/submissions/e1ff6ab9-f83c-4780-ad15-c27fdd142209

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_UnramifiedDefs
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeRangeNormUnits
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_LocalIndex
import Definitions.Def_GroundTheory_LocalFields_UnramifiedNormSurj
import Theorems.Thm_GroundTheory_LocalField_map_normUnits_unitFiltrationUnits
import Theorems.Thm_GroundTheory_Global_div_mem_unitFiltration_iff
import Theorems.Thm_GroundTheory_Global_filtrationComplete_unitFiltration
import Theorems.Thm_GroundTheory_Global_filtrationSeparated_unitFiltration


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
open ValuativeRel IsLocalRing Filter Polynomial
open GroundTheory.Global (filtrationComplete_unitFiltration filtrationSeparated_unitFiltration
  div_mem_unitFiltration_iff)
variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
variable [IsUnramified K L]
namespace GroundTheory.LocalField
theorem _root_.solution :
    unitFiltrationUnits K 0 ≤ (normUnits K L).range := by
  rw [← map_normUnits_unitFiltrationUnits (L := L) 0]
  exact Subgroup.map_le_range _ _
end GroundTheory.LocalField
