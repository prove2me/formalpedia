-- Prove2me | solution 1 for GroundTheory.LocalField.isDiscreteModule_units
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:09:25.242901+00:00
-- url     : https://prove2.me/submissions/0ba515bb-90ec-4140-84f2-d3fac4eb2d75

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsOpenSubgroupMemFixedModule
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeRangeNormUnits
import Definitions.Def_GroundTheory_LocalFields_LocalAxiomTransport
import Definitions.Def_GroundTheory_LocalFields_LocalAxiomDictionary
import Theorems.Thm_GroundTheory_LocalField_mem_fixedModule_units_iff
import Theorems.Thm_GroundTheory_LocalField_Abstract_isDiscreteModule_iff


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
theorem _root_.solution : IsDiscreteModule G Ωˣ := by
  rw [isDiscreteModule_iff]
  intro a
  have : FiniteDimensional K (IntermediateField.adjoin K {(a : Ω)}) :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral _)
  exact ⟨fixingOpenSubgroup (IntermediateField.adjoin K {(a : Ω)}),
    (mem_fixedModule_units_iff _ a).2 (IntermediateField.subset_adjoin K _ rfl)⟩
end GroundTheory.LocalField
