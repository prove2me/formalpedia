-- Prove2me | solution 1 for GroundTheory.Global.InfinitePlace.algebraMap_trace_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:47:56.135126+00:00
-- url     : https://prove2.me/submissions/f9be9f83-f73d-480d-94e9-dd6d0870e3ea

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Infinite
import Theorems.Thm_GroundTheory_Global_InfinitePlace_algebraMap_trace_eq_trace_tmul
import Theorems.Thm_GroundTheory_Global_InfinitePlace_trace_tensor_eq_sum

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
open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped NumberField.LiesOver TensorProduct
open GroundTheory.Global.InfinitePlace
variable {K L : Type*} [Field K] [Field L] [Algebra K L] (v : InfinitePlace K)
variable [NumberField K] [NumberField L]
open scoped Classical
namespace GroundTheory.Global.InfinitePlace
theorem _root_.solution (l : L) :
    algebraMap K v.Completion (Algebra.trace K L l) =
      ∑ w : v.placesOver L,
        Algebra.trace v.Completion _ (l : (w : InfinitePlace L).Completion) := by
  rw [algebraMap_trace_eq_trace_tmul, trace_tensor_eq_sum]
  simp
end GroundTheory.Global.InfinitePlace
