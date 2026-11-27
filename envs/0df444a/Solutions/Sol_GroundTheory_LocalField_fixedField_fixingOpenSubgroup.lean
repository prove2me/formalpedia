-- Prove2me | solution 1 for GroundTheory.LocalField.fixedField_fixingOpenSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:46:43.723263+00:00
-- url     : https://prove2.me/submissions/c37ed3c9-e8ab-4ed3-ab27-15697d64de11

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
theorem _root_.solution (L : IntermediateField K Ω) [FiniteDimensional K L] :
    fixedField (fixingOpenSubgroup L : Subgroup G) = L :=
  InfiniteGalois.fixedField_fixingSubgroup L
end GroundTheory.LocalField
