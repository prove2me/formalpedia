-- Prove2me | solution 2 for GlobalTheory.gaussVal_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:39:38.160721+00:00
-- url     : https://prove2.me/submissions/253c405d-efbd-4ec6-918b-11c1f768911f

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
theorem _root_.solution (a : R) (f : MvPolynomial σ R) :
    gaussVal v (a • f) = v a * gaussVal v f := by
  rw [smul_eq_C_mul, map_mul, gaussVal_C]
end GlobalTheory
