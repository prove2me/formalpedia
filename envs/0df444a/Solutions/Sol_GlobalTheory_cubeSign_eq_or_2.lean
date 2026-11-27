-- Prove2me | solution 2 for GlobalTheory.cubeSign_eq_or
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:38:10.221625+00:00
-- url     : https://prove2.me/submissions/0f8d36bd-3865-4ccb-a098-cce984464bad

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits
universe v v' u u'
open GlobalTheory
variable {ι : Type} [LinearOrder ι]
namespace GlobalTheory
theorem _root_.solution (t : Finset ι) (i : ι) : cubeSign t i = 1 ∨ cubeSign t i = -1 :=
  neg_one_pow_eq_or ℤ _
end GlobalTheory
