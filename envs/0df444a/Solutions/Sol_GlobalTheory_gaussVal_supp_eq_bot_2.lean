-- Prove2me | solution 2 for GlobalTheory.gaussVal_supp_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:39:40.440262+00:00
-- url     : https://prove2.me/submissions/d664cfa2-995a-46f3-a16d-f8a1d2bf4344

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
variable [LinearOrderedCommMonoidWithZero Γ₀] [Nontrivial Γ₀] (v : Valuation K Γ₀)
namespace GlobalTheory
theorem _root_.solution : (gaussVal (σ := σ) v).supp = ⊥ :=
  gaussVal_supp_eq_bot_of_supp v (valuation_supp_eq_bot v)
end GlobalTheory
