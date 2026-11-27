-- Prove2me | solution 2 for GlobalTheory.gaussAbs_sumAlgEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:39:58.166216+00:00
-- url     : https://prove2.me/submissions/61577e7f-5156-4082-b536-fcdce5ca898d

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
variable {R σ τ : Type*} [CommRing R]
variable [Nontrivial R] (a : AbsoluteValue R ℝ) (ha : IsNonarchimedean a)
namespace GlobalTheory
theorem _root_.solution (f : MvPolynomial (σ ⊕ τ) R) :
    gaussAbs (gaussAbs a ha) (isNonarchimedean_gaussAbs a ha) (sumAlgEquiv R σ τ f) =
      gaussAbs a ha f :=
  congrArg NNReal.toReal (gaussVal_sumAlgEquiv (absValuation a ha) f)
end GlobalTheory
