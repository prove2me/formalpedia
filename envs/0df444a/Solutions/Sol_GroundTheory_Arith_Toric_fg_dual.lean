-- Prove2me | solution 1 for GroundTheory.Arith.Toric.fg_dual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:27:29.570834+00:00
-- url     : https://prove2.me/submissions/e1fbf713-4423-4074-8551-1e5c3353855a

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_ExistsDualNegOfNotMemHullFinset
import Theorems.Thm_GroundTheory_Arith_Toric_fg_dual_finset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Toric
open Module PointedCone
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {V W : Type*} [AddCommGroup V] [Module 𝕜 V] [AddCommGroup W] [Module 𝕜 W]
variable {M N : Type*} [AddCommGroup M] [Module 𝕜 M] [AddCommGroup N] [Module 𝕜 N]
namespace GroundTheory.Arith.Toric
theorem _root_.solution [FiniteDimensional 𝕜 N] (p : M →ₗ[𝕜] N →ₗ[𝕜] 𝕜) {C : PointedCone 𝕜 M}
    (hC : C.FG) : (dual p (C : Set M)).FG := by
  obtain ⟨S, rfl⟩ := hC
  rw [dual_hull]
  exact fg_dual_finset p S
end GroundTheory.Arith.Toric
