-- Prove2me | solution 1 for GlobalTheory.LengthCommensurable.signedLength_le_signedLength
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:08:07.838503+00:00
-- url     : https://prove2.me/submissions/bda5dba7-d299-4778-a2f4-227bffa7cdc1

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
theorem _root_.solution {A' B' : Submodule R V} (h : LengthCommensurable A B)
    (h' : LengthCommensurable A' B') (hA : A ≤ A') (hB : B' ≤ B) :
    signedLength A B ≤ signedLength A' B' := by
  have h₁ := ENat.toNat_le_toNat (relLength_le_relLength hA hB) h'.1
  have h₂ := ENat.toNat_le_toNat (relLength_le_relLength hB hA) h.2
  unfold signedLength
  omega
end GlobalTheory.LengthCommensurable
