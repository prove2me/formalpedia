-- Prove2me | solution 2 for GlobalTheory.gaussValAlg_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:39:08.632441+00:00
-- url     : https://prove2.me/submissions/b26a6a8c-450c-4004-a6a6-907e9d34d305

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TensorContentEqPolyContentScalarCoeffs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
noncomputable section
open scoped NNReal TensorProduct
variable {R G Γ₀ : Type*} [Ring R] [LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀)
variable [AddMonoid G] [UniqueSums G]
namespace GlobalTheory
theorem _root_.solution (f : AddMonoidAlgebra R G) :
    gaussValAlg v f = f.coeff.support.sup fun m => v (f.coeff m) := rfl
end GlobalTheory
