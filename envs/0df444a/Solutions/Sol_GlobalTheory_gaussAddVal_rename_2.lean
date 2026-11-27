-- Prove2me | solution 2 for GlobalTheory.gaussAddVal_rename
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:38:59.285999+00:00
-- url     : https://prove2.me/submissions/4c31f5ce-4d65-4f5b-b2e3-b49260b00bd9

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
variable {R Γ σ τ : Type*} [CommRing R] [LinearOrderedAddCommMonoidWithTop Γ]
  (v : AddValuation R Γ)
namespace GlobalTheory
theorem _root_.solution {e : σ → τ} (he : Function.Injective e) (f : MvPolynomial σ R) :
    gaussAddVal v (rename e f) = gaussAddVal v f :=
  gaussVal_rename (AddValuation.toValuation v) he f
end GlobalTheory
