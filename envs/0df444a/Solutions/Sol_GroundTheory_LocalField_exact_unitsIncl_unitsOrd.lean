-- Prove2me | solution 1 for GroundTheory.LocalField.exact_unitsIncl_unitsOrd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:08:13.899156+00:00
-- url     : https://prove2.me/submissions/4d8433d9-b95b-4004-bd97-5b355ff89ebd

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_HerbrandCyclic
import Definitions.Def_GroundTheory_LocalFields_HilbertCyclic
import Definitions.Def_GroundTheory_LocalFields_UnitsGalois
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeAndRangePowLe
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeRangeNormUnits
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Cyclic
import Definitions.Def_GroundTheory_LocalFields_HerbrandLocalBase
import Theorems.Thm_GroundTheory_LocalField_ord_eq_zero_iff_mem_range_unitsIncl

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
theorem _root_.solution :
    Function.Exact (MonoidHom.toAdditive (unitsIncl L)) (unitsOrd L) := by
  intro y
  change ord ((y.toMul : Lˣ) : L) = 0 ↔ _
  rw [ord_eq_zero_iff_mem_range_unitsIncl]
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨Additive.ofMul u, Additive.toMul.injective hu⟩
  · rintro ⟨u, rfl⟩
    exact ⟨u.toMul, rfl⟩
end GroundTheory.LocalField
