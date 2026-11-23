-- Prove2me | solution 1 for GlobalTheory.polyContent_le_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:44:00.049801+00:00
-- url     : https://prove2.me/submissions/0b740335-8fc9-4ebe-af57-94786786c5fc

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
open MvPolynomial Module
variable {R Γ₀ ι κ σ : Type*} [CommRing R] [LinearOrderedCommMonoidWithZero Γ₀]
  (v : Valuation R Γ₀) {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable (b : Basis ι R M)
namespace GlobalTheory
theorem _root_.solution {c : (σ →₀ ℕ) →₀ M} {γ : Γ₀} :
    polyContent v b c ≤ γ ↔ ∀ m, basisVal v b (c m) ≤ γ :=
  coeffSup_le_iff (basisVal_zero v b)
end GlobalTheory
