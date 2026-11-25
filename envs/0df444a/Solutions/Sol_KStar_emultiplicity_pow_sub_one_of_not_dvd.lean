-- Prove2me | solution 1 for KStar.emultiplicity_pow_sub_one_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:25:44.591863+00:00
-- url     : https://prove2.me/submissions/c4e114de-7868-4aec-bd7e-95f4aec84c8d

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_TotallyRealRoots

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open KStar
variable {R : Type*} [CommRing R] [IsDomain R]
namespace KStar
theorem _root_.solution {p u : R} (hp : Prime p) (hu : p ∣ u - 1)
    {n : ℕ} (hn : ¬ p ∣ (n : R)) : emultiplicity p (u ^ n - 1) = emultiplicity p (u - 1) := by
  have hx : ¬ p ∣ u := by
    intro h
    have : p ∣ u - (u - 1) := dvd_sub h hu
    rw [sub_sub_cancel] at this
    exact hp.not_isUnit (isUnit_of_dvd_one this)
  have := emultiplicity_pow_sub_pow_of_prime hp (y := 1) (by simpa using hu) hx hn
  simpa using this
end KStar
