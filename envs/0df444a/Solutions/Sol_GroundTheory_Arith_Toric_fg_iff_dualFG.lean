-- Prove2me | solution 1 for GroundTheory.Arith.Toric.fg_iff_dualFG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:45:31.419243+00:00
-- url     : https://prove2.me/submissions/97155461-91ef-4315-a25a-9329710b94d5

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_ExistsDualNegOfNotMemHullFinset
import Theorems.Thm_GroundTheory_Arith_Toric_fg_dual_finset
import Theorems.Thm_GroundTheory_Arith_Toric_fg_dual
import Theorems.Thm_GroundTheory_Arith_Toric_dual_dual_flip_of_fg

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
theorem _root_.solution [FiniteDimensional 𝕜 M] [FiniteDimensional 𝕜 N]
    (p : M →ₗ[𝕜] N →ₗ[𝕜] 𝕜) (hp : Function.Surjective p) {C : PointedCone 𝕜 N} :
    C.FG ↔ C.DualFG p := by
  constructor
  · intro hC
    obtain ⟨T, hT⟩ := fg_dual p.flip hC
    refine ⟨T, ?_⟩
    rw [← dual_hull]
    change dual p (Submodule.span _ (T : Set M) : Set M) = C
    rw [hT]
    exact dual_dual_flip_of_fg p hp hC
  · rintro ⟨s, rfl⟩
    exact fg_dual_finset p s
end GroundTheory.Arith.Toric
