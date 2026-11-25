-- Prove2me | solution 1 for GroundTheory.LocalField.coe_tateNorm_units
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:12:53.265062+00:00
-- url     : https://prove2.me/submissions/8d2c31bf-5fe3-4d0f-96c3-01c32f1b4af9

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_HerbrandCyclic
import Definitions.Def_GroundTheory_LocalFields_HilbertCyclic
import Definitions.Def_GroundTheory_LocalFields_UnitsGalois
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeAndRangePowLe
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeRangeNormUnits
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Cyclic
import Definitions.Def_GroundTheory_LocalFields_HerbrandLocalBase
import Theorems.Thm_GroundTheory_LocalField_algebraMap_norm_eq_prod
import Theorems.Thm_GroundTheory_LocalField_tateNorm_apply


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
variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
namespace GroundTheory.LocalField
theorem _root_.solution (x : Lˣ) :
    ((tateNorm (L ≃ₐ[K] L) Lˣ x : Lˣ) : L) = algebraMap K L (Algebra.norm K (x : L)) := by
  rw [algebraMap_norm_eq_prod, tateNorm_apply, Units.coe_prod]
  rfl
end GroundTheory.LocalField
