-- Prove2me | solution 1 for GlobalTheory.gaussVal_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:59:02.190062+00:00
-- url     : https://prove2.me/submissions/c1e6b491-7465-4e11-bbf4-51fe4a1cd02b

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
variable {R S Γ₀ σ τ : Type*} [CommRing R] [CommRing S] [LinearOrderedCommMonoidWithZero Γ₀]
  (v : Valuation R Γ₀)
namespace GlobalTheory
theorem _root_.solution (f : MvPolynomial σ R) :
    gaussVal v f = f.support.sup fun m => v (coeff m f) := rfl
end GlobalTheory
