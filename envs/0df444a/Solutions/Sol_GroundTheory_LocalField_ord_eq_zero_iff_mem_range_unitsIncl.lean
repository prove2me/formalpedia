-- Prove2me | solution 1 for GroundTheory.LocalField.ord_eq_zero_iff_mem_range_unitsIncl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:50:10.881167+00:00
-- url     : https://prove2.me/submissions/a7b59995-0261-48e0-b0cd-8d0b269d5afd

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_HerbrandCyclic
import Definitions.Def_GroundTheory_LocalFields_HilbertCyclic
import Definitions.Def_GroundTheory_LocalFields_UnitsGalois
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeAndRangePowLe
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeRangeNormUnits
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Cyclic
import Definitions.Def_GroundTheory_LocalFields_HerbrandLocalBase
import Theorems.Thm_GroundTheory_LocalField_ord_eq_zero_iff_mem


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
open ValuativeRel GroundTheory.GroupCoh GroundTheory.Global
variable {L : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
namespace GroundTheory.LocalField
theorem _root_.solution (x : Lˣ) :
    ord (x : L) = 0 ↔ x ∈ (unitsIncl L).range := by
  rw [ord_eq_zero_iff_mem, unitFiltrationUnits, unitFiltration_zero, ← MonoidHom.range_eq_map]
end GroundTheory.LocalField
