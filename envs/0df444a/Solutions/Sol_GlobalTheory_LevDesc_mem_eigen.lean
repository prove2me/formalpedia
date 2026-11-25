-- Prove2me | solution 1 for GlobalTheory.LevDesc.mem_eigen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:02:57.513618+00:00
-- url     : https://prove2.me/submissions/bddf3f7c-1cc8-4aeb-b839-d25d33309652

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
theorem _root_.solution {χ : G →* Kˣ} {F : R} : F ∈ eigen st χ ↔ ∀ h, st h F = ((χ h : Kˣ) : K) • F := Iff.rfl
end GlobalTheory.LevDesc
