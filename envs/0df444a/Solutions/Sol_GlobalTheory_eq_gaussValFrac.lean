-- Prove2me | solution 1 for GlobalTheory.eq_gaussValFrac
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T12:58:44.76262+00:00
-- url     : https://prove2.me/submissions/6d546db6-9999-4a4a-bd06-ceb43f1bbe00

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
variable {K Γ₀ σ τ : Type*} [Field K]
variable [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)
variable {F : Type*} [Field F] [Algebra (MvPolynomial σ K) F]
  [IsFractionRing (MvPolynomial σ K) F]

theorem solution {w : Valuation F Γ₀}
    (h : ∀ f : MvPolynomial σ K, w (algebraMap _ F f) = gaussVal v f) :
    w = gaussValFrac v σ F := by
  ext x
  obtain ⟨f, g, rfl⟩ := IsLocalization.exists_mk'_eq (nonZeroDivisors (MvPolynomial σ K)) x
  simp [IsFractionRing.mk'_eq_div, h, gaussValFrac_algebraMap]
