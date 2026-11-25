-- Prove2me | solution 1 for GroundTheory.PAdicHodge.normTrace_algebraMap_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:29:30.187371+00:00
-- url     : https://prove2.me/submissions/ab957903-f9d0-401b-bfd0-9494b3cc4a01

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
import Theorems.Thm_GroundTheory_PAdicHodge_normTrace_smul

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
theorem _root_.solution (a : F) (y : Ω) :
    normTrace F (algebraMap F Ω a * y) = algebraMap F Ω a * normTrace F y := by
  rw [← Algebra.smul_def, normTrace_smul, Algebra.smul_def]
end GroundTheory.PAdicHodge
