-- Prove2me | solution 1 for GroundTheory.Global.InfinitePlace.algebraMap_trace_eq_trace_tmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:07:27.633541+00:00
-- url     : https://prove2.me/submissions/0b8f7310-c049-4cdb-8f78-864e5f181746

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
    algebraMap K v.Completion (Algebra.trace K L l) =
      Algebra.trace v.Completion _ ((1 : v.Completion) ⊗ₜ[K] l) := by
  rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul,
    LinearMap.trace_baseChange]
end GroundTheory.Global.InfinitePlace
