-- Prove2me | solution 1 for GroundTheory.LocalField.finiteDimensional_extendScalars
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:20:53.739309+00:00
-- url     : https://prove2.me/submissions/553778af-ebab-4303-a6b2-006c7627dad9

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
variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
variable (K' L' : Subgroup (Ω ≃ₐ[K] Ω)) {E F : IntermediateField K Ω} (hEF : E ≤ F)
  (hK : E.fixingSubgroup = K') (hL : F.fixingSubgroup = L')
omit [IsGalois K Ω]
namespace GroundTheory.LocalField
theorem _root_.solution [FiniteDimensional K F] :
    FiniteDimensional E (extendScalars hEF) :=
  have : FiniteDimensional K (extendScalars hEF) := inferInstanceAs (FiniteDimensional K F)
  Module.Finite.of_restrictScalars_finite K E (extendScalars hEF)
end GroundTheory.LocalField
