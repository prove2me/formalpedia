-- Prove2me | solution 1 for GlobalTheory.polyContent_le_iff_coord
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:17:18.48979+00:00
-- url     : https://prove2.me/submissions/228e86a1-3d54-4e16-8904-2a75b9410b64

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TensorContentEqPolyContentScalarCoeffs
import Theorems.Thm_GlobalTheory_polyContent_le_iff

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
    polyContent v b c ≤ γ ↔ ∀ m i, v (b.repr (c m) i) ≤ γ := by
  simp only [polyContent_le_iff, basisVal_le_iff]
end GlobalTheory
