-- Prove2me | solution 1 for GroundTheory.Global.InfinitePlace.algebraMap_norm_eq_norm_tmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:07:26.939433+00:00
-- url     : https://prove2.me/submissions/6eb02a17-a35e-4508-8826-a8201886e9f5

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Infinite

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
namespace GroundTheory.Global.InfinitePlace
theorem _root_.solution (l : L) :
    algebraMap K v.Completion (Algebra.norm K l) =
      Algebra.norm v.Completion ((1 : v.Completion) ⊗ₜ[K] l) := by
  rw [Algebra.norm_apply, Algebra.norm_apply, ← Algebra.baseChange_lmul, LinearMap.det_baseChange]
end GroundTheory.Global.InfinitePlace
