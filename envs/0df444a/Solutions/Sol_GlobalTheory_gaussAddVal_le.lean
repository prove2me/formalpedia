-- Prove2me | solution 1 for GlobalTheory.gaussAddVal_le
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T12:44:50.629337+00:00
-- url     : https://prove2.me/submissions/f25af202-1870-481a-b31e-d2530262c2ca

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
variable {R Γ σ τ : Type*} [CommRing R] [LinearOrderedAddCommMonoidWithTop Γ]
  (v : AddValuation R Γ)

theorem solution (f : MvPolynomial σ R) (m : σ →₀ ℕ) :
    gaussAddVal v f ≤ v (coeff m f) := by
  have h := le_gaussVal (AddValuation.toValuation v) f m
  rw [gaussAddVal, ← AddValuation.ofValuation_toValuation (v := v)]
  rw [AddValuation.ofValuation_apply, AddValuation.ofValuation_apply]
  exact OrderDual.ofDual_le_ofDual.mpr (Multiplicative.toAdd_le.mpr h)
