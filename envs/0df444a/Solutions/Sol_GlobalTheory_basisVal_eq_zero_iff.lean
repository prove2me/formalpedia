-- Prove2me | solution 1 for GlobalTheory.basisVal_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:14:51.376037+00:00
-- url     : https://prove2.me/submissions/2bca6311-e051-4033-a3d7-07790cd52572

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
theorem _root_.solution (hv : v.supp = ⊥) {x : M} : basisVal v b x = 0 ↔ x = 0 := by
  rw [basisVal, coeffSup_eq_zero_iff v.map_zero, ← b.repr.map_eq_zero_iff, Finsupp.ext_iff]
  simp only [← Valuation.mem_supp_iff, hv, Ideal.mem_bot, Finsupp.zero_apply]
end GlobalTheory
