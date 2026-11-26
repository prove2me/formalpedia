-- Prove2me | solution 1 for GlobalTheory.gaussVal_smul
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:29:32.816808+00:00
-- url     : https://prove2.me/submissions/5de17eca-e100-4056-b3b7-075e8780b85e

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
theorem _root_.solution (a : R) (f : MvPolynomial σ R) :
    gaussVal v (a • f) = v a * gaussVal v f := by
  first
    | (rw [MvPolynomial.smul_eq_C_mul, map_mul, GlobalTheory.gaussVal_C])

