-- Prove2me | solution 1 for Ideal.list_prod_le_getElem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:44:05.991897+00:00
-- url     : https://prove2.me/submissions/f8ad0672-b980-4886-a373-7b3d3345d5b6

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_SpanSingletonProduct

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Ideal
namespace Ideal
theorem _root_.solution {R : Type*} [CommRing R] (L : List (Ideal R)) (i : ℕ)
    (hi : i < L.length) : L.prod ≤ (L[i]'hi) := by
  revert i hi
  induction L with
  | nil =>
      intro i hi
      simp at hi
  | cons A L ih =>
      intro i hi
      cases i with
      | zero =>
          simp only [List.prod_cons, List.getElem_cons_zero]
          exact le_trans Ideal.mul_le_inf inf_le_left
      | succ i' =>
          have hi' : i' < L.length := by simpa using hi
          simp only [List.prod_cons, List.getElem_cons_succ]
          exact le_trans (le_trans Ideal.mul_le_inf inf_le_right) (ih i' hi')
end Ideal
