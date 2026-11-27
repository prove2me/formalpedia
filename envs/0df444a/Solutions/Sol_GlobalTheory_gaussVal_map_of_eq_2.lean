-- Prove2me | solution 2 for GlobalTheory.gaussVal_map_of_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:39:25.465929+00:00
-- url     : https://prove2.me/submissions/2652ec44-2922-4898-afc8-522e5097e8cf

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
variable {R S Γ₀ σ τ : Type*} [CommRing R] [CommRing S] [LinearOrderedCommMonoidWithZero Γ₀]
  (v : Valuation R Γ₀)
namespace GlobalTheory
theorem _root_.solution (w : Valuation S Γ₀) (φ : R →+* S) (h : ∀ a, w (φ a) = v a)
    (f : MvPolynomial σ R) : gaussVal w (map φ f) = gaussVal v f := by
  rw [gaussVal_map, show w.comap φ = v from Valuation.ext h]
end GlobalTheory
