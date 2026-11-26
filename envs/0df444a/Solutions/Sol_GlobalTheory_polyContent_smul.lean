-- Prove2me | solution 1 for GlobalTheory.polyContent_smul
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T13:44:13.551801+00:00
-- url     : https://prove2.me/submissions/ea7cd6bc-d86f-469b-b509-791926890308

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

theorem solution (a : R) (c : (σ →₀ ℕ) →₀ M) :
    polyContent v b (a • c) = v a * polyContent v b c :=
  coeffSup_eq_mul_of_forall (basisVal_zero v b) (basisVal_zero v b) fun i => by
    rw [Finsupp.smul_apply, basisVal_smul]
