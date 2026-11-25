-- Prove2me | solution 1 for GlobalTheory.LevDesc.ps_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:04:16.415802+00:00
-- url     : https://prove2.me/submissions/4306b10b-aef9-4a57-86ce-80c48bcaae1d

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
theorem _root_.solution (u : R) (F : G → R) : ps st u F = ∑ h, F h * st h u := by
  rw [ps, LinearMap.sum_apply]; rfl
end GlobalTheory.LevDesc
