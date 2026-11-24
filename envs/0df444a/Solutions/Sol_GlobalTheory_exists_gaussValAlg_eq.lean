-- Prove2me | solution 1 for GlobalTheory.exists_gaussValAlg_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:42:38.85603+00:00
-- url     : https://prove2.me/submissions/8b16d7c0-68f9-4cac-9a36-c3f4013b4f9a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TensorContentEqPolyContentScalarCoeffs
import Theorems.Thm_GlobalTheory_exists_coeffSup_eq

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
    ∃ m, gaussValAlg v f = v (f.coeff m) :=
  haveI : Nonempty G := ⟨0⟩
  exists_coeffSup_eq v.map_zero f.coeff
end GlobalTheory
