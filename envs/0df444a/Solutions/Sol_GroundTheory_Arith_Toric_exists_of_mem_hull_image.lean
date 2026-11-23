-- Prove2me | solution 1 for GroundTheory.Arith.Toric.exists_of_mem_hull_image
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:38:23.027729+00:00
-- url     : https://prove2.me/submissions/203241a8-a493-4fd6-b460-c63f6f4a8815

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_ExistsDualNegOfNotMemHullFinset

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
namespace GroundTheory.Arith.Toric
theorem _root_.solution (φ : V →ₗ[𝕜] W) {s : Set V} {y : W}
    (hy : y ∈ hull 𝕜 (φ '' s)) : ∃ z ∈ hull 𝕜 s, φ z = y := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨z, hz, rfl⟩ := hy
    exact ⟨z, subset_hull hz, rfl⟩
  | zero => exact ⟨0, zero_mem _, map_zero φ⟩
  | add y y' _ _ h h' =>
    obtain ⟨z, hz, rfl⟩ := h
    obtain ⟨z', hz', rfl⟩ := h'
    exact ⟨z + z', add_mem hz hz', map_add φ z z'⟩
  | smul c y _ h =>
    obtain ⟨z, hz, rfl⟩ := h
    exact ⟨(c : 𝕜) • z, smul_mem _ c.2 hz, by rw [map_smul]; rfl⟩
end GroundTheory.Arith.Toric
