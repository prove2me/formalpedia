-- Prove2me | solution 1 for GroundTheory.LocalField.baseUnitsEquiv_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:29:59.80339+00:00
-- url     : https://prove2.me/submissions/c64e021e-0986-4a1c-a8d0-8ba6cd07895a

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsOpenSubgroupMemFixedModule
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeRangeNormUnits
import Definitions.Def_GroundTheory_LocalFields_LocalAxiomTransport
import Definitions.Def_GroundTheory_LocalFields_LocalAxiomDictionary
import Theorems.Thm_GroundTheory_LocalField_coe_norm_top
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
open GroundTheory GroundTheory.LocalField
open Abstract IntermediateField
variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
local notation "G" => Ω ≃ₐ[K] Ω
variable (L : IntermediateField K Ω)
variable [FiniteDimensional K L]
namespace GroundTheory.LocalField
theorem _root_.solution [(L.fixingSubgroup.subgroupOf ⊤).FiniteIndex]
    (a : fixedModule Ωˣ L.fixingSubgroup) :
    baseUnitsEquiv (norm Ωˣ ⊤ L.fixingSubgroup a) = normUnits K L (fixedModuleUnitsEquiv L a) := by
  ext
  apply (algebraMap K Ω).injective
  rw [algebraMap_baseUnitsEquiv, coe_norm_top, coe_normUnits]
end GroundTheory.LocalField
