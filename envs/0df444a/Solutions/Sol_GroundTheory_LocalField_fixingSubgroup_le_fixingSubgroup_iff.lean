-- Prove2me | solution 1 for GroundTheory.LocalField.fixingSubgroup_le_fixingSubgroup_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:48:44.488872+00:00
-- url     : https://prove2.me/submissions/a0908ab1-e243-441f-8b90-16bdb3f95dc1

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
theorem _root_.solution {L L' : IntermediateField K Ω} :
    L.fixingSubgroup ≤ L'.fixingSubgroup ↔ L' ≤ L := by
  constructor
  · intro h
    rw [← InfiniteGalois.fixedField_fixingSubgroup L, ← InfiniteGalois.fixedField_fixingSubgroup L']
    exact IntermediateField.fixedField_antitone h
  · intro h
    exact IntermediateField.fixingSubgroup_antitone h
end GroundTheory.LocalField
