-- Prove2me | solution 2 for GlobalTheory.polyContent_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:41:03.998659+00:00
-- url     : https://prove2.me/submissions/4a6ecaba-4b75-4e86-a4ff-7e85dee5d936

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TensorContentEqPolyContentScalarCoeffs
import Theorems.Thm_GlobalTheory_basisVal_eq_zero_iff

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
theorem _root_.solution (hv : v.supp = ⊥) {c : (σ →₀ ℕ) →₀ M} :
    polyContent v b c = 0 ↔ c = 0 := by
  rw [polyContent, coeffSup_eq_zero_iff (basisVal_zero v b), Finsupp.ext_iff]
  simp only [basisVal_eq_zero_iff v b hv, Finsupp.zero_apply]
end GlobalTheory
