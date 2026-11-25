-- Prove2me | solution 1 for GroundTheory.Global.InfinitePlace.trace_tensor_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:10:43.984605+00:00
-- url     : https://prove2.me/submissions/10e4bf77-13a4-40cb-916a-a2659e73241f

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Infinite
import Theorems.Thm_GroundTheory_Global_Algebra_trace_pi

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
theorem _root_.solution (x : v.Completion ⊗[K] L) :
    Algebra.trace v.Completion _ x =
      ∑ w : v.placesOver L, Algebra.trace v.Completion _ (tensorPiHom v x w) := by
  rw [← Algebra.trace_eq_of_algEquiv (tensorPiEquiv (L := L) v) x, tensorPiEquiv_apply,
    GroundTheory.Global.Algebra.trace_pi]
end GroundTheory.Global.InfinitePlace
