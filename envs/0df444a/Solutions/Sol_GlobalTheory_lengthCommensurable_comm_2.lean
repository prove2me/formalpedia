-- Prove2me | solution 2 for GlobalTheory.lengthCommensurable_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:41:58.717522+00:00
-- url     : https://prove2.me/submissions/351743f5-a720-4bbb-bdce-303a023a4602

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
theorem _root_.solution : LengthCommensurable A B ↔ LengthCommensurable B A :=
  ⟨.symm, .symm⟩
end GlobalTheory
