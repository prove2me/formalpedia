-- Prove2me | solution 1 for GroundTheory.LocalField.fixingOpenSubgroup_fixedField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:46:46.868801+00:00
-- url     : https://prove2.me/submissions/c130fbf3-265c-4f45-974a-b5bb37c3c7f6

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsOpenSubgroupMemFixedModule
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeRangeNormUnits
import Definitions.Def_GroundTheory_LocalFields_LocalAxiomTransport
import Definitions.Def_GroundTheory_LocalFields_LocalAxiomDictionary

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
variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
local notation "G" => Ω ≃ₐ[K] Ω
variable [IsGalois K Ω]
namespace GroundTheory.LocalField
theorem _root_.solution (U : OpenSubgroup G) :
    fixingOpenSubgroup (fixedField (U : Subgroup G)) = U :=
  OpenSubgroup.ext fun σ => by
    rw [← OpenSubgroup.mem_toSubgroup, coe_fixingOpenSubgroup,
      fixingSubgroup_fixedField_openSubgroup]
    rfl
end GroundTheory.LocalField
