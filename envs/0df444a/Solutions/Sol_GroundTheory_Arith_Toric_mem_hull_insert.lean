-- Prove2me | solution 1 for GroundTheory.Arith.Toric.mem_hull_insert
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:36:24.022739+00:00
-- url     : https://prove2.me/submissions/000b2bf3-0283-48c0-8e50-73f853413ad0

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
theorem _root_.solution {a x : V} {s : Set V} :
    x ∈ hull 𝕜 (insert a s) ↔ ∃ c : 𝕜, 0 ≤ c ∧ ∃ y ∈ hull 𝕜 s, x = c • a + y := by
  rw [Submodule.mem_span_insert]
  constructor
  · rintro ⟨c, y, hy, rfl⟩
    exact ⟨c, c.2, y, hy, rfl⟩
  · rintro ⟨c, hc, y, hy, rfl⟩
    exact ⟨⟨c, hc⟩, y, hy, rfl⟩
end GroundTheory.Arith.Toric
