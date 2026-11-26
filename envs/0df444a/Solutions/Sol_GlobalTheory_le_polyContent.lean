-- Prove2me | solution 1 for GlobalTheory.le_polyContent
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:48:37.179821+00:00
-- url     : https://prove2.me/submissions/1fc736a1-3afa-491c-aa54-6e5d5dcee52d

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
theorem _root_.solution (c : (σ →₀ ℕ) →₀ M) (m : σ →₀ ℕ) :
    basisVal v b (c m) ≤ polyContent v b c := by
  first
    | (refine GlobalTheory.le_coeffSup (N := GlobalTheory.basisVal v b) ?_ c m
       unfold GlobalTheory.basisVal
       simp)

