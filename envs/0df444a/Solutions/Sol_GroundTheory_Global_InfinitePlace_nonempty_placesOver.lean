-- Prove2me | solution 1 for GroundTheory.Global.InfinitePlace.nonempty_placesOver
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:06:52.321641+00:00
-- url     : https://prove2.me/submissions/21e9c130-ba94-4aac-97a6-528ffdb6cfcc

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Infinite
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_Splitting
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_SplittingInfinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Global
open NumberField Module
open scoped NumberField.LiesOver TensorProduct
open GroundTheory.Global.InfinitePlace
variable {K : Type*} [Field K] (L : Type*) [Field L] [Algebra K L]
variable {L} (v : NumberField.InfinitePlace K)
variable [NumberField K] [NumberField L]
variable (L)
namespace GroundTheory.Global.InfinitePlace
theorem _root_.solution : Nonempty (v.placesOver L) := by
  classical
  by_contra h
  rw [not_nonempty_iff] at h
  have := sum_finrank_completion (L := L) v
  rw [Finset.univ_eq_empty, Finset.sum_empty] at this
  exact (Module.finrank_pos (R := K) (M := L)).ne this
end GroundTheory.Global.InfinitePlace
