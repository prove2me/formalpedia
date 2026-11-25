-- Prove2me | solution 1 for GroundTheory.Arith.Toric.bot_isFaceOf_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:52:52.706978+00:00
-- url     : https://prove2.me/submissions/a5ebbc2b-ceef-40db-bc7d-24a4135350ff

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_ExistsDualNegOfNotMemHullFinset
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_IsFaceOfIffExistsEqExposedFace

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
variable {V : Type*} [AddCommGroup V] [Module 𝕜 V]
namespace GroundTheory.Arith.Toric
theorem _root_.solution {σ : PointedCone 𝕜 V} :
    (⊥ : PointedCone 𝕜 V).IsFaceOf σ ↔ (σ : ConvexCone 𝕜 V).Salient := by
  constructor
  · intro h x hx hx0 hnx
    have : x ∈ (⊥ : PointedCone 𝕜 V) :=
      h.mem_of_add_mem_left hx hnx (by simp)
    exact hx0 ((Submodule.mem_bot _).1 this)
  · intro hs
    refine ⟨bot_le, fun {x y a} hx hy ha h => ?_⟩
    rw [Submodule.mem_bot] at h ⊢
    have hy' : y = -(a • x) := eq_neg_of_add_eq_zero_right h
    have hax : a • x ∈ σ := smul_mem _ ha.le hx
    by_contra hx0
    have hax0 : a • x ≠ 0 := smul_ne_zero ha.ne' hx0
    exact hs _ hax hax0 (hy' ▸ hy)
end GroundTheory.Arith.Toric
