-- Prove2me | solution 1 for GlobalTheory.gaussVal_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:15:24.116158+00:00
-- url     : https://prove2.me/submissions/9ea15dd7-c83e-4717-b762-f3a270cab081

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
theorem _root_.solution (w : Valuation S Γ₀) (φ : R →+* S) (f : MvPolynomial σ R) :
    gaussVal w (map φ f) = gaussVal (w.comap φ) f :=
  eq_of_forall_ge_iff fun γ => by simp [gaussVal_le_iff, coeff_map]
end GlobalTheory
