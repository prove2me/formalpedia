-- Prove2me | solution 1 for GlobalTheory.LevDesc.tr_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:55:05.769406+00:00
-- url     : https://prove2.me/submissions/7d5ca9fe-892d-4982-9092-6e2670729111

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
theorem _root_.solution (χ : G →* Kˣ) (F : R) : tr st χ F = ∑ h, (((χ h)⁻¹ : Kˣ) : K) • st h F := by
  rw [tr, LinearMap.sum_apply]; rfl
end GlobalTheory.LevDesc
