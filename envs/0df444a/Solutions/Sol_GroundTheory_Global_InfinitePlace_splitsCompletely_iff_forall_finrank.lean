-- Prove2me | solution 1 for GroundTheory.Global.InfinitePlace.splitsCompletely_iff_forall_finrank
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:09:30.75546+00:00
-- url     : https://prove2.me/submissions/57cf8e31-47a4-417b-83fc-186ff6863a47

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Infinite
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_Splitting
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_SplittingInfinite
import Theorems.Thm_GroundTheory_Global_InfinitePlace_isUnramified_iff_finrank_eq_one

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
namespace GroundTheory.Global.InfinitePlace
theorem _root_.solution :
    SplitsCompletely L v ↔
      ∀ w : v.placesOver L, finrank v.Completion (w : NumberField.InfinitePlace L).Completion = 1 :=
  ⟨fun h w ↦ (isUnramified_iff_finrank_eq_one v w.1).1 (h w.1 w.2),
    fun h w hw ↦ have := hw; (isUnramified_iff_finrank_eq_one v w).2 (h ⟨w, hw⟩)⟩
end GroundTheory.Global.InfinitePlace
