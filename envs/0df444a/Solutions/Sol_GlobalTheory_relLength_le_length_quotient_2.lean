-- Prove2me | solution 2 for GlobalTheory.relLength_le_length_quotient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:41:03.949237+00:00
-- url     : https://prove2.me/submissions/108abd29-62f9-435a-b8b1-e2691f99cae8

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
theorem _root_.solution (A B : Submodule R V) :
    relLength A B ≤ Module.length R (V ⧸ B) := by
  rw [← relLength_top_left]
  exact relLength_mono_left le_top B
end GlobalTheory
