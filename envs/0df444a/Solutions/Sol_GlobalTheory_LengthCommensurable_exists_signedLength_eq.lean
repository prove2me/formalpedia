-- Prove2me | solution 1 for GlobalTheory.LengthCommensurable.exists_signedLength_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:00:27.825513+00:00
-- url     : https://prove2.me/submissions/c77ae70b-c266-4ebc-9c0c-5038fe131c33

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
theorem _root_.solution (h : LengthCommensurable A B) :
    ∃ m n : ℕ, relLength A B = m ∧ relLength B A = n ∧ signedLength A B = (m : ℤ) - n :=
  ⟨_, _, (ENat.coe_toNat h.1).symm, (ENat.coe_toNat h.2).symm, rfl⟩
end GlobalTheory.LengthCommensurable
