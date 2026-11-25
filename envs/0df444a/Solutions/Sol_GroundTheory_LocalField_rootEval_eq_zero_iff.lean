-- Prove2me | solution 1 for GroundTheory.LocalField.rootEval_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:15:24.842067+00:00
-- url     : https://prove2.me/submissions/83b84d9b-9481-4b1c-aa5f-d68dfcf62696

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LubinTateReciprocity_RootEval

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
open PowerSeries
variable {B : Type*} [CommRing B] {I : Ideal B} {P : Polynomial B}
variable [IsAdicComplete I B] (hP : P.IsDistinguishedAt I)
namespace GroundTheory.LocalField
theorem _root_.solution (F : B⟦X⟧) :
    rootEval hP F = 0 ↔ F ∈ Ideal.span {(P : B⟦X⟧)} := by
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  change hP.algEquivQuotient.symm _ = 0 ↔ _
  rw [map_eq_zero_iff _ hP.algEquivQuotient.symm.injective]
  rfl
end GroundTheory.LocalField
