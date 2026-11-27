-- Prove2me | solution 2 for GlobalTheory.gaussVal_gaussValFrac_sumAlgEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:39:21.000751+00:00
-- url     : https://prove2.me/submissions/159f70f4-17fb-4dfc-92b0-e7f807fb804e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TensorContentEqPolyContentScalarCoeffs
import Theorems.Thm_GlobalTheory_gaussVal_map

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
open MvPolynomial
variable {K Γ₀ σ τ : Type*} [Field K]
variable [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)
variable {F : Type*} [Field F] [Algebra (MvPolynomial σ K) F]
  [IsFractionRing (MvPolynomial σ K) F]
namespace GlobalTheory
theorem _root_.solution (f : MvPolynomial (τ ⊕ σ) K) :
    gaussVal (gaussValFrac v σ F) (map (algebraMap _ F) (sumAlgEquiv K τ σ f)) =
      gaussVal v f := by
  rw [gaussVal_map, gaussValFrac_comap, gaussVal_sumAlgEquiv]
end GlobalTheory
