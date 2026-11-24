-- Prove2me | solution 1 for GlobalTheory.LevDesc.trivMod_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:41:31.70034+00:00
-- url     : https://prove2.me/submissions/565d88ad-4301-436b-9476-87e7c0ac1b49

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsRightActFunPull

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LevDesc
variable {O : Type} [CommRing O] (N : Type) [AddCommGroup N] [Module O N]
variable {N} {I J : Ideal O}
namespace GlobalTheory.LevDesc
theorem _root_.solution {J' : Ideal O} (h : J ≤ J') : trivMod N I J ≤ trivMod N I J' :=
  fun _ hγ q => Submodule.smul_mono_left h (hγ q)
end GlobalTheory.LevDesc
