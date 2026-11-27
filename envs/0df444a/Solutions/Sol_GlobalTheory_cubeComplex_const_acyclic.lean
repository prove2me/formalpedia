-- Prove2me | solution 1 for GlobalTheory.cubeComplex_const_acyclic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:37:51.718803+00:00
-- url     : https://prove2.me/submissions/7046fa56-34e3-4ffb-bfb7-562fca2e42f0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Theorems.Thm_GlobalTheory_cubeComplex_const_exactAt

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
theorem _root_.solution [Nonempty ι] (M : ModuleCat.{v} R) :
    (cubeComplex (Cube.const ι M)).Acyclic :=
  cubeComplex_const_exactAt M
end GlobalTheory
