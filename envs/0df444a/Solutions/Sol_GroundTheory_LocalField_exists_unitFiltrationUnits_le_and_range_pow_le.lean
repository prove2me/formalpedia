-- Prove2me | solution 1 for GroundTheory.LocalField.exists_unitFiltrationUnits_le_and_range_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:47:36.979454+00:00
-- url     : https://prove2.me/submissions/8e918988-b7e0-4188-8f50-690dd379ab21

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeAndRangePowLe
import Theorems.Thm_GroundTheory_LocalField_exists_unitFiltrationUnits_le
import Theorems.Thm_GroundTheory_LocalField_exists_range_pow_le

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
theorem _root_.solution {H : Subgroup Kˣ} [H.FiniteIndex]
    (hH : IsOpen (H : Set Kˣ)) :
    (∃ n, unitFiltrationUnits K n ≤ H) ∧ ∃ m, m ≠ 0 ∧ (powMonoidHom m : Kˣ →* Kˣ).range ≤ H :=
  ⟨exists_unitFiltrationUnits_le hH, exists_range_pow_le⟩
end GroundTheory.LocalField
