-- Prove2me | solution 2 for GlobalTheory.antitone_relLength_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:35:47.68992+00:00
-- url     : https://prove2.me/submissions/968d11d8-5764-40eb-b4f4-ecab4925585a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]
namespace GlobalTheory
theorem _root_.solution (A : Submodule R V) : Antitone (relLength A) :=
  fun _ _ h => relLength_anti_right A h
end GlobalTheory
