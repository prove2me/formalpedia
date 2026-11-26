-- Prove2me | solution 1 for GlobalTheory.gaussAbs_sumAlgEquiv
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T12:52:47.606313+00:00
-- url     : https://prove2.me/submissions/8454b7bd-0aa6-498b-aa5e-f2df13d8da49

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

theorem solution (f : MvPolynomial (σ ⊕ τ) R) :
    gaussAbs (gaussAbs a ha) (isNonarchimedean_gaussAbs a ha) (sumAlgEquiv R σ τ f) =
      gaussAbs a ha f := by
  have hval :
      absValuation (gaussAbs (σ := τ) a ha) (isNonarchimedean_gaussAbs (σ := τ) a ha) =
        gaussVal (σ := τ) (absValuation a ha) := by
    refine Valuation.ext fun x => ?_
    apply NNReal.coe_injective
    simp [coe_absValuation, gaussAbs_apply]
  simp [gaussAbs_apply, hval, gaussVal_sumAlgEquiv]
