-- Prove2me | solution 1 for GroundTheory.LocalField.ker_unitsToTateZero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:49:20.545+00:00
-- url     : https://prove2.me/submissions/97e4384c-c986-4685-b733-3592b01868ad

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_HerbrandCyclic
import Definitions.Def_GroundTheory_LocalFields_HilbertCyclic
import Definitions.Def_GroundTheory_LocalFields_UnitsGalois
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeAndRangePowLe
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeRangeNormUnits
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Cyclic
import Definitions.Def_GroundTheory_LocalFields_HerbrandLocalBase
import Theorems.Thm_GroundTheory_LocalField_coe_tateNorm_units
import Theorems.Thm_GroundTheory_LocalField_coe_normUnits
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.coe_normUnits



set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel GroundTheory.GroupCoh GroundTheory.Global
variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
namespace GroundTheory.LocalField
theorem _root_.solution : (unitsToTateZero (K := K) (L := L)).ker = (normUnits K L).range := by
  ext a
  rw [MonoidHom.mem_ker, unitsToTateZero, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, MonoidHom.mem_range, MonoidHom.mem_range]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y, Units.ext ((algebraMap K L).injective ?_)⟩
    rw [coe_normUnits, ← coe_tateNorm_units, hy]
    rfl
  · rintro ⟨y, rfl⟩
    refine ⟨y, Units.ext ?_⟩
    rw [coe_tateNorm_units]
    rfl
end GroundTheory.LocalField
