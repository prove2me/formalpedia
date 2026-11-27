-- Prove2me | solution 1 for GroundTheory.Global.InfinitePlace.algebraMap_norm_eq_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:47:51.755267+00:00
-- url     : https://prove2.me/submissions/5a66f8f9-97ac-43f4-a5d0-8b721b7c6cea

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Infinite
import Theorems.Thm_GroundTheory_Global_InfinitePlace_algebraMap_norm_eq_norm_tmul
import Theorems.Thm_GroundTheory_Global_InfinitePlace_norm_tensor_eq_prod

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
    algebraMap K v.Completion (Algebra.norm K l) =
      ∏ w : v.placesOver L, Algebra.norm v.Completion (l : (w : InfinitePlace L).Completion) := by
  rw [algebraMap_norm_eq_norm_tmul, norm_tensor_eq_prod]
  simp
end GroundTheory.Global.InfinitePlace
