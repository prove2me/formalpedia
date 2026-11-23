-- Prove2me | solution 1 for GroundTheory.LocalField.continuous_restrictAb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:59:56.041554+00:00
-- url     : https://prove2.me/submissions/7e85def0-b21a-44cb-a21d-6b39bc78a41e

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_MaximalAbelianExtension

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
open IntermediateField
open scoped commutatorElement
variable {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] [IsGalois F Ω]
variable (E : IntermediateField F Ω) [Normal F E]
namespace GroundTheory.LocalField
theorem _root_.solution (h : E ≤ maximalAbelianExtension F Ω) : Continuous (restrictAb E h) := by
  have h1 : Continuous (QuotientGroup.lift _ (AlgEquiv.restrictNormalHom (F := F) (K₁ := Ω) E)
      (closure_commutator_le_ker_restrictNormalHom E h)) :=
    Continuous.quotient_lift (InfiniteGalois.restrictNormalHom_continuous E) _
  exact h1.comp (topologicalAbelianizationEquiv F Ω).symm.continuous
end GroundTheory.LocalField
