-- Prove2me | solution 2 for GlobalTheory.relLength_pos_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:43:30.442808+00:00
-- url     : https://prove2.me/submissions/68af6d53-4d4e-43e9-a9bb-a05c2097747f

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
theorem _root_.solution {A B : Submodule R V} : 0 < relLength A B ↔ ¬ A ≤ B := by
  rw [pos_iff_ne_zero, ne_eq, relLength_eq_zero_iff]
end GlobalTheory
