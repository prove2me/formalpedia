-- Prove2me | solution 2 for GlobalTheory.exists_gaussAddVal_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:38:18.732819+00:00
-- url     : https://prove2.me/submissions/b18326f8-3da9-45a4-b30c-6414f9a861c6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TensorContentEqPolyContentScalarCoeffs
import Theorems.Thm_GlobalTheory_exists_gaussVal_eq

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
theorem _root_.solution (f : MvPolynomial σ R) : ∃ m, gaussAddVal v f = v (coeff m f) :=
  exists_gaussVal_eq (AddValuation.toValuation v) f
end GlobalTheory
