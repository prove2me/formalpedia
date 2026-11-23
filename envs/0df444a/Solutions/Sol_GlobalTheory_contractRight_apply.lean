-- Prove2me | solution 1 for GlobalTheory.contractRight_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:24:37.251854+00:00
-- url     : https://prove2.me/submissions/91104de1-c7c8-4c37-95b5-692498aaed8b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DvdTraceOfBalancedTensor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
variable {O H : Type*} [CommRing O] [CommRing H] [Algebra O H]
namespace GlobalTheory
theorem _root_.solution (Θ : H ⊗[O] H) (α : Module.Dual O H) :
    contractRight Θ α = TensorProduct.rid O H (LinearMap.lTensor H α Θ) := rfl
end GlobalTheory
