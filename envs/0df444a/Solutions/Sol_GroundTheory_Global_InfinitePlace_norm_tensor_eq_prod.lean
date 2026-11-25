-- Prove2me | solution 1 for GroundTheory.Global.InfinitePlace.norm_tensor_eq_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:12:29.281377+00:00
-- url     : https://prove2.me/submissions/f2cdeb55-f048-4831-b870-6c0de01f54f7

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Infinite
import Theorems.Thm_GroundTheory_Global_Algebra_norm_pi

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
    Algebra.norm v.Completion x =
      ∏ w : v.placesOver L, Algebra.norm v.Completion (tensorPiHom v x w) := by
  rw [← Algebra.norm_eq_of_algEquiv (tensorPiEquiv (L := L) v) x, tensorPiEquiv_apply,
    GroundTheory.Global.Algebra.norm_pi]
end GroundTheory.Global.InfinitePlace
