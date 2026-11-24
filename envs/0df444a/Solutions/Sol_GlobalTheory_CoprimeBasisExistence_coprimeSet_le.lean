-- Prove2me | solution 1 for GlobalTheory.CoprimeBasisExistence.coprimeSet_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:53:29.354806+00:00
-- url     : https://prove2.me/submissions/ad454d39-b957-4574-a707-e9257eb4e701

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IsPrincipalIdealRingLoc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CoprimeBasisExistence
open NumberField nonZeroDivisors
namespace GlobalTheory.CoprimeBasisExistence
theorem _root_.solution (A : Type*) [CommRing A] [IsDomain A] [CharZero A] (m : ℕ) :
    coprimeSet A m ≤ A⁰ := by
  rintro _ ⟨k, hk, _, rfl⟩
  exact mem_nonZeroDivisors_of_ne_zero (Nat.cast_ne_zero.2 hk.ne')
end GlobalTheory.CoprimeBasisExistence
