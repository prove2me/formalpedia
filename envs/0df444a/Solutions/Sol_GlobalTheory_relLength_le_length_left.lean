-- Prove2me | solution 1 for GlobalTheory.relLength_le_length_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:31:18.387689+00:00
-- url     : https://prove2.me/submissions/131d39a5-88e2-438b-bdb3-cd870ac22512

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
theorem _root_.solution (A B : Submodule R V) : relLength A B ≤ Module.length R A := by
  rw [← relLength_bot_right]
  exact relLength_anti_right A bot_le
end GlobalTheory
