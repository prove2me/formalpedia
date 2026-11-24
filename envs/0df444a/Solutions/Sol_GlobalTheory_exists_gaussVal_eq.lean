-- Prove2me | solution 1 for GlobalTheory.exists_gaussVal_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:51:52.589788+00:00
-- url     : https://prove2.me/submissions/9ff9c4f7-3db4-48bc-b31d-efa9e5da55d5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TensorContentEqPolyContentScalarCoeffs
import Theorems.Thm_GlobalTheory_exists_gaussValAlg_eq

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
theorem _root_.solution (f : MvPolynomial σ R) : ∃ m, gaussVal v f = v (coeff m f) :=
  exists_gaussValAlg_eq v f
end GlobalTheory
