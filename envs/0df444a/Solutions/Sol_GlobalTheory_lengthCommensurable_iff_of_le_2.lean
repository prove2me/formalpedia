-- Prove2me | solution 2 for GlobalTheory.lengthCommensurable_iff_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:40:38.304905+00:00
-- url     : https://prove2.me/submissions/9a974bbe-cd33-4df2-9cdb-d11971eec7c8

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
variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V] {A B : Submodule R V}
namespace GlobalTheory
theorem _root_.solution (h : A ≤ B) :
    LengthCommensurable A B ↔ relLength B A ≠ ⊤ := by
  simp [LengthCommensurable, relLength_eq_zero_of_le h]
end GlobalTheory
