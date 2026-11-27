-- Prove2me | solution 1 for GlobalTheory.lengthCommensurable_iff_isFiniteLength
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:40:35.04102+00:00
-- url     : https://prove2.me/submissions/84d3cf0d-9291-4702-8eda-b517b1ef855f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
import Theorems.Thm_GlobalTheory_relLength_ne_top_iff

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
      IsFiniteLength R (A ⧸ B.submoduleOf A) ∧ IsFiniteLength R (B ⧸ A.submoduleOf B) := by
  rw [LengthCommensurable, relLength_ne_top_iff, relLength_ne_top_iff]
end GlobalTheory
