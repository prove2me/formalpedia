-- Prove2me | solution 1 for GlobalTheory.LevDesc.IsRightAct.equiv_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:04:06.058597+00:00
-- url     : https://prove2.me/submissions/f2cfad85-6e89-4c1f-aa7c-a76584207973

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
namespace IsRightAct
theorem _root_.solution {st : G → R →ₐ[K] R} (hs : IsRightAct st) (h : G) (x : R) :
    hs.equiv h x = st h x := rfl
end IsRightAct
end GlobalTheory.LevDesc
