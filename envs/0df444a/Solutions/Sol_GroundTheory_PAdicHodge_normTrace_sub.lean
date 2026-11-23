-- Prove2me | solution 1 for GroundTheory.PAdicHodge.normTrace_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:34:08.860296+00:00
-- url     : https://prove2.me/submissions/517921a7-e195-470f-ac0b-aa60f0bc0319

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace

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
theorem _root_.solution (y z : Ω) : normTrace F (y - z) = normTrace F y - normTrace F z :=
  map_sub (normTraceₗ F) y z
end GroundTheory.PAdicHodge
