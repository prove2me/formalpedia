-- Prove2me | solution 1 for GroundTheory.Arith.Toric.fg_dual_finset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:18:20.698657+00:00
-- url     : https://prove2.me/submissions/60ed883c-0286-4c49-9c42-f480dc85a07d

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_ExistsDualNegOfNotMemHullFinset
import Theorems.Thm_GroundTheory_Arith_Toric_fg_top
import Theorems.Thm_GroundTheory_Arith_Toric_fg_inf_halfspace

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
theorem _root_.solution [FiniteDimensional 𝕜 N] (p : M →ₗ[𝕜] N →ₗ[𝕜] 𝕜) (s : Finset M) :
    (dual p (s : Set M)).FG := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using fg_top
  | insert a s _ ih =>
    rw [Finset.coe_insert, dual_insert, dual_singleton, inf_comm]
    exact fg_inf_halfspace ih (p a)
end GroundTheory.Arith.Toric
