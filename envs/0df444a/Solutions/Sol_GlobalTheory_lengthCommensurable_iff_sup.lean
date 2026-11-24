-- Prove2me | solution 1 for GlobalTheory.lengthCommensurable_iff_sup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:14:43.572803+00:00
-- url     : https://prove2.me/submissions/41f73cce-b2dc-4ece-9613-3b66c538a609

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
theorem _root_.solution :
    LengthCommensurable A B ↔
      LengthCommensurable (A ⊔ B) B ∧ LengthCommensurable (A ⊔ B) A := by
  rw [lengthCommensurable_iff_of_ge (le_sup_right : B ≤ A ⊔ B),
    lengthCommensurable_iff_of_ge (le_sup_left : A ≤ A ⊔ B),
    relLength_sup_left, relLength_sup_left', LengthCommensurable]
end GlobalTheory
