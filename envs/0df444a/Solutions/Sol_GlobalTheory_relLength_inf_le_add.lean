-- Prove2me | solution 1 for GlobalTheory.relLength_inf_le_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:01:18.706518+00:00
-- url     : https://prove2.me/submissions/01f29ff4-3d3d-4d49-9cb5-5319ffca3342

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthCommensurableIffOfLeOfLe

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
theorem _root_.solution (A B C : Submodule R V) :
    relLength A (B ⊓ C) ≤ relLength A B + relLength A C := by
  rw [relLength_inf_eq_add]
  gcongr
  exact inf_le_left
end GlobalTheory
