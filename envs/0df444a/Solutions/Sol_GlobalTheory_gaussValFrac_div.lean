-- Prove2me | solution 1 for GlobalTheory.gaussValFrac_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:58:59.474378+00:00
-- url     : https://prove2.me/submissions/5373d3cb-a995-4cd6-b2b3-cefd1dc31d51

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
open MvPolynomial
variable {K Γ₀ σ τ : Type*} [Field K]
variable [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)
variable {F : Type*} [Field F] [Algebra (MvPolynomial σ K) F]
  [IsFractionRing (MvPolynomial σ K) F]
namespace GlobalTheory
theorem _root_.solution (f g : MvPolynomial σ K) :
    gaussValFrac v σ F (algebraMap _ F f / algebraMap _ F g) = gaussVal v f / gaussVal v g := by
  simp
end GlobalTheory
