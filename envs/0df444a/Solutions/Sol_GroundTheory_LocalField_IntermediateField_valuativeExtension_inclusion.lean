-- Prove2me | solution 1 for GroundTheory.LocalField.IntermediateField.valuativeExtension_inclusion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:46:41.568799+00:00
-- url     : https://prove2.me/submissions/d726e328-d346-46be-bde3-86b802fdd774

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_FiniteExtension
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_IntermediateField
import Definitions.Def_GroundTheory_LocalFields_SeparableClosure

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
open ValuativeRel Topology Filter Polynomial
variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [ValuativeRel Ω]
namespace GroundTheory.LocalField
namespace IntermediateField
theorem _root_.solution {E F : IntermediateField K Ω} (h : E ≤ F) :
    letI := (IntermediateField.inclusion h).toRingHom.toAlgebra
    ValuativeExtension E F :=
  letI := (IntermediateField.inclusion h).toRingHom.toAlgebra
  ⟨fun a b ↦ by
    rw [← IntermediateField.coe_vle_coe_iff (L := Ω) a b,
      ← IntermediateField.coe_vle_coe_iff (L := Ω)]
    rfl⟩
end IntermediateField
end GroundTheory.LocalField
