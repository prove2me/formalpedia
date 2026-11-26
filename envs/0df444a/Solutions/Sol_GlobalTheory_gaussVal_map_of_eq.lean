-- Prove2me | solution 1 for GlobalTheory.gaussVal_map_of_eq
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T12:55:00.763815+00:00
-- url     : https://prove2.me/submissions/83023761-c48a-487b-b69a-114daa8a9b5c

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
variable {R S Γ₀ σ τ : Type*} [CommRing R] [CommRing S] [LinearOrderedCommMonoidWithZero Γ₀]
  (v : Valuation R Γ₀)

theorem solution (w : Valuation S Γ₀) (φ : R →+* S) (h : ∀ a, w (φ a) = v a)
    (f : MvPolynomial σ R) : gaussVal w (map φ f) = gaussVal v f := by
  refine le_antisymm ?_ ?_
  · exact (gaussVal_le_iff w).mpr fun m => by
      rw [coeff_map, h]
      exact le_gaussVal v f m
  · exact (gaussVal_le_iff v).mpr fun m => by
      rw [← h, ← coeff_map]
      exact le_gaussVal w (map φ f) m
