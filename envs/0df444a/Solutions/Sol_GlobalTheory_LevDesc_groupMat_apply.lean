-- Prove2me | solution 1 for GlobalTheory.LevDesc.groupMat_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:00:05.820944+00:00
-- url     : https://prove2.me/submissions/7b34e8d9-48a1-4654-8509-cf959d58e3cd

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
variable {G K R : Type} [Group G] [Field K] [CommRing R] [Algebra K R]
variable (st : G → R →ₐ[K] R)
namespace GlobalTheory.LevDesc
theorem _root_.solution (u : R) (h g : G) : groupMat st u h g = st (h * g) u := rfl
end GlobalTheory.LevDesc
