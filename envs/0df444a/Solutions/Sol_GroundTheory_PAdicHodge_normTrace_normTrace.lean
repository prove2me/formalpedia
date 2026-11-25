-- Prove2me | solution 1 for GroundTheory.PAdicHodge.normTrace_normTrace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:29:31.669334+00:00
-- url     : https://prove2.me/submissions/22088aeb-45fb-4157-99db-6cffa013bb6b

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
import Theorems.Thm_GroundTheory_PAdicHodge_normTraceF_normTrace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open Polynomial Module IntermediateField
noncomputable section
variable (F : Type*) {Ω : Type*} [Field F] [Field Ω] [Algebra F Ω]
variable [CharZero F] [Algebra.IsIntegral F Ω]
namespace GroundTheory.PAdicHodge
theorem _root_.solution (E : Type*) [Field E] [Algebra F E] [Algebra E Ω]
    [IsScalarTower F E Ω] [FiniteDimensional F E] (y : Ω) :
    normTrace F (normTrace E y) = normTrace F y := by
  rw [normTrace, normTraceF_normTrace, normTrace]
end GroundTheory.PAdicHodge
