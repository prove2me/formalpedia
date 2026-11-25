-- Prove2me | solution 1 for GlobalTheory.LevDesc.ph_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:04:15.015251+00:00
-- url     : https://prove2.me/submissions/49e46830-afb2-4fec-a2ec-37eec1808ee8

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
variable [Fintype G]
namespace GlobalTheory.LevDesc
theorem _root_.solution (χ : G →* Kˣ) (u f : R) (h : G) : ph st χ u f h = tr st χ (f * st h u) := rfl
end GlobalTheory.LevDesc
