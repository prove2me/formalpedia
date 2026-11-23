-- Prove2me | solution 1 for GroundTheory.Arith.Toric.nonneg_of_mem_hull
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:28:15.664796+00:00
-- url     : https://prove2.me/submissions/4cb12cf4-2279-4109-b058-6d35d86894f0

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
theorem _root_.solution {f : Dual 𝕜 V} {s : Set V} (hs : ∀ y ∈ s, 0 ≤ f y) {x : V}
    (hx : x ∈ hull 𝕜 s) : 0 ≤ f x := by
  have h : hull 𝕜 s ≤ (positive 𝕜 𝕜).comap f :=
    Submodule.span_le.2 fun y hy => by simpa [mem_comap, mem_positive] using hs y hy
  simpa [mem_comap, mem_positive] using h hx
end GroundTheory.Arith.Toric
