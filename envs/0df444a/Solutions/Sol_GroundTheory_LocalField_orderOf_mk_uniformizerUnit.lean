-- Prove2me | solution 1 for GroundTheory.LocalField.orderOf_mk_uniformizerUnit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:46:52.282628+00:00
-- url     : https://prove2.me/submissions/bc1437aa-a0e0-41ab-aa5c-3ec2dba24a0e

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_UnramifiedDefs
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeRangeNormUnits
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_LocalIndex
import Definitions.Def_GroundTheory_LocalFields_UnramifiedNormSurj
import Theorems.Thm_GroundTheory_LocalField_index_range_normUnits
import Theorems.Thm_GroundTheory_LocalField_zpowers_mk_uniformizerUnit
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
theorem _root_.solution {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) :
    orderOf (QuotientGroup.mk (uniformizerUnit hϖ) : Kˣ ⧸ (normUnits K L).range) =
      Module.finrank K L := by
  rw [orderOf_eq_card_of_forall_mem_zpowers (fun q ↦ by
    rw [zpowers_mk_uniformizerUnit hϖ]; exact Subgroup.mem_top q)]
  exact index_range_normUnits
end GroundTheory.LocalField
