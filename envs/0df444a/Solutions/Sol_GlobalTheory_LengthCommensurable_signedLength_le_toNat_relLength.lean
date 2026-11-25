-- Prove2me | solution 1 for GlobalTheory.LengthCommensurable.signedLength_le_toNat_relLength
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:02:12.265275+00:00
-- url     : https://prove2.me/submissions/a5826239-fc1f-40bd-b232-6aff663413c9

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
open GlobalTheory.LengthCommensurable
namespace GlobalTheory.LengthCommensurable
theorem _root_.solution (_h : LengthCommensurable A B) :
    signedLength A B ≤ (relLength A B).toNat :=
  sub_le_self _ (Int.natCast_nonneg _)
end GlobalTheory.LengthCommensurable
