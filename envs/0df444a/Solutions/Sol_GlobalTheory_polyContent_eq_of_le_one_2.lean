-- Prove2me | solution 2 for GlobalTheory.polyContent_eq_of_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:40:59.33771+00:00
-- url     : https://prove2.me/submissions/7e719333-093d-4ba0-8037-db0f5f17c2b7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TensorContentEqPolyContentScalarCoeffs
import Theorems.Thm_GlobalTheory_basisVal_eq_of_le_one

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
open MvPolynomial Module
variable {R Γ₀ ι κ σ : Type*} [CommRing R] [LinearOrderedCommMonoidWithZero Γ₀]
  (v : Valuation R Γ₀) {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable (b : Basis ι R M)
namespace GlobalTheory
theorem _root_.solution (b' : Basis κ R M) (h : ∀ i, basisVal v b' (b i) ≤ 1)
    (h' : ∀ j, basisVal v b (b' j) ≤ 1) (c : (σ →₀ ℕ) →₀ M) :
    polyContent v b c = polyContent v b' c := by
  rw [polyContent, polyContent, funext (basisVal_eq_of_le_one v b b' h h')]
end GlobalTheory
