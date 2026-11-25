-- Prove2me | solution 1 for GroundTheory.LocalField.mem_fixedModule_units_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:25:10.498269+00:00
-- url     : https://prove2.me/submissions/a2e437ae-edbb-49bc-830d-080c61e672df

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsOpenSubgroupMemFixedModule
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeRangeNormUnits
import Definitions.Def_GroundTheory_LocalFields_LocalAxiomTransport
import Definitions.Def_GroundTheory_LocalFields_LocalAxiomDictionary
import Theorems.Thm_GroundTheory_LocalField_Abstract_mem_fixedModule


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
open Abstract IntermediateField
variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
local notation "G" => Ω ≃ₐ[K] Ω
namespace GroundTheory.LocalField
theorem _root_.solution (L : IntermediateField K Ω) (a : Ωˣ) :
    a ∈ fixedModule Ωˣ L.fixingSubgroup ↔ (a : Ω) ∈ L := by
  rw [mem_iff_forall_fixingSubgroup, mem_fixedModule]
  refine forall₂_congr fun σ _ => ?_
  rw [Units.ext_iff]
  rfl
end GroundTheory.LocalField
