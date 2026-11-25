-- Prove2me | solution 1 for GlobalTheory.LevDesc.isRightAct_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:04:12.619137+00:00
-- url     : https://prove2.me/submissions/71fba8e4-d497-49ee-927e-bdbc83bc05ab

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
namespace GlobalTheory.LevDesc
theorem _root_.solution (ρ : G →* (R →ₐ[K] R)) : IsRightAct (fun h => ρ h⁻¹) :=
  ⟨fun x => by simp, fun h h' x => by simp only [mul_inv_rev, map_mul]; rfl⟩
end GlobalTheory.LevDesc
