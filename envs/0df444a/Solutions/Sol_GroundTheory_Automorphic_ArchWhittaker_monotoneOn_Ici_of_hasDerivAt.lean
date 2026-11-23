-- Prove2me | solution 1 for GroundTheory.Automorphic.ArchWhittaker.monotoneOn_Ici_of_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:39:00.608063+00:00
-- url     : https://prove2.me/submissions/1a0cf027-369b-4185-9e4a-ba903541e307

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ArchimedeanWhittaker_WronskianEqZeroOfModerate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.ArchWhittaker
open Filter Topology Set
namespace GroundTheory.Automorphic.ArchWhittaker
theorem _root_.solution {u u' : ℝ → ℝ} {a : ℝ}
    (hu : ∀ y ≥ a, HasDerivAt u (u' y) y) (hpos : ∀ y ≥ a, 0 ≤ u' y) : MonotoneOn u (Ici a) := by
  refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := u') (convex_Ici a)
    (fun y hy => (hu y hy).continuousAt.continuousWithinAt) (fun y hy => ?_) (fun y hy => ?_)
  · rw [interior_Ici] at hy
    exact (hu y (le_of_lt hy)).hasDerivWithinAt
  · rw [interior_Ici] at hy
    exact hpos y (le_of_lt hy)
end GroundTheory.Automorphic.ArchWhittaker
