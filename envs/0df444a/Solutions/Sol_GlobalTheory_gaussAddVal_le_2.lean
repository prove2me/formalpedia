-- Prove2me | solution 2 for GlobalTheory.gaussAddVal_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:38:52.874795+00:00
-- url     : https://prove2.me/submissions/75ec42ed-cc3a-44ce-a336-c6e523270157

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TensorContentEqPolyContentScalarCoeffs
import Theorems.Thm_GlobalTheory_le_gaussAddVal_iff

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
theorem _root_.solution (f : MvPolynomial σ R) (m : σ →₀ ℕ) : gaussAddVal v f ≤ v (coeff m f) :=
  (le_gaussAddVal_iff v).mp le_rfl m
end GlobalTheory
