-- Prove2me | solution 2 for GlobalTheory.monotone_relLength_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:42:46.842485+00:00
-- url     : https://prove2.me/submissions/8938865e-549f-4b93-974d-e06985290192

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
theorem _root_.solution (B : Submodule R V) : Monotone fun A => relLength A B :=
  fun _ _ h => relLength_mono_left h B
end GlobalTheory
