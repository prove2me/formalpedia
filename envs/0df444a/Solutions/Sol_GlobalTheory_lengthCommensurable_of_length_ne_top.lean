-- Prove2me | solution 1 for GlobalTheory.lengthCommensurable_of_length_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:38:53.311699+00:00
-- url     : https://prove2.me/submissions/0d13269d-3172-409c-8498-8be7280e3c7a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
import Theorems.Thm_GlobalTheory_relLength_le_length_left

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
theorem _root_.solution (h : Module.length R V ≠ ⊤) (A B : Submodule R V) :
    LengthCommensurable A B := by
  have key : ∀ C D : Submodule R V, relLength C D ≠ ⊤ := fun C D =>
    ne_top_of_le_ne_top h ((relLength_le_length_left C D).trans
      (Module.length_le_of_injective C.subtype C.injective_subtype))
  exact ⟨key A B, key B A⟩
end GlobalTheory
