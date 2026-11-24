-- Prove2me | solution 1 for GlobalTheory.cubeComplex_const_exactAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:34:01.735926+00:00
-- url     : https://prove2.me/submissions/f55eb995-fe48-4d5d-be8d-4740a454dea4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Theorems.Thm_GlobalTheory_cubeComplex_exactAt_of_bijective

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
variable {ι : Type} [LinearOrder ι] {R : Type u} [Ring R]
namespace GlobalTheory
theorem _root_.solution [Nonempty ι] (M : ModuleCat.{v} R) (p : ℕ) :
    (cubeComplex (Cube.const ι M)).ExactAt p :=
  cubeComplex_exactAt_of_bijective (Cube.const ι M) (Classical.arbitrary ι)
    (fun _ _ => Function.bijective_id) p
end GlobalTheory
