-- Prove2me | solution 1 for GroundTheory.Global.InfinitePlace.splitsCompletely_iff_isFiniteSplit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:46:14.804663+00:00
-- url     : https://prove2.me/submissions/9237b552-7f15-418c-83f6-38cd5a0eecf7

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Infinite
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_Splitting
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_SplittingInfinite
import Theorems.Thm_GroundTheory_Global_InfinitePlace_splitsCompletely_iff_forall_finrank
import Theorems.Thm_GroundTheory_Global_isFiniteSplit_pi_iff
import Theorems.Thm_GroundTheory_Global_splitsCompletely_iff_forall_finrank


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
namespace GroundTheory.Global.InfinitePlace
theorem _root_.solution :
    SplitsCompletely L v ↔ Algebra.IsFiniteSplit v.Completion (v.Completion ⊗[K] L) := by
  rw [splitsCompletely_iff_forall_finrank, ← isFiniteSplit_pi_iff]
  exact ⟨fun h ↦ .of_algEquiv (tensorPiEquiv (L := L) v).symm,
    fun h ↦ .of_algEquiv (tensorPiEquiv (L := L) v)⟩
end GroundTheory.Global.InfinitePlace
