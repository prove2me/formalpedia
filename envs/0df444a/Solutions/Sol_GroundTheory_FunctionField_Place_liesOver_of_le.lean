-- Prove2me | solution 1 for GroundTheory.FunctionField.Place.liesOver_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:10:42.528797+00:00
-- url     : https://prove2.me/submissions/a65274f8-c779-4ebd-8d22-2682724c8868

import Mathlib
import Definitions.Def_GroundTheory_FunctionField_PlaceBasic
import Definitions.Def_GroundTheory_FunctionField_PlaceAbove
import Theorems.Thm_GroundTheory_FunctionField_Place_liesOver_iff_comap_eq
import Theorems.Thm_GroundTheory_FunctionField_Place_eq_of_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.FunctionField
open GroundTheory.FunctionField.Place
variable {k K K' : Type*} [Field k] [Field K] [Field K'] [Algebra k K] [Algebra k K']
  [Algebra K K'] [IsScalarTower k K K']
namespace GroundTheory.FunctionField.Place
theorem _root_.solution [IsFunctionField k K] [Algebra.IsAlgebraic K K'] {w : Place k K'}
    {v : Place k K} (h : ∀ x ∈ v.ring, algebraMap K K' x ∈ w.ring) : w.LiesOver v := by
  have := Place.eq_of_le (v := v) (w := w.comap) fun x hx => ValuationSubring.mem_comap.2 (h x hx)
  exact liesOver_iff_comap_eq.2 this.symm
end GroundTheory.FunctionField.Place
