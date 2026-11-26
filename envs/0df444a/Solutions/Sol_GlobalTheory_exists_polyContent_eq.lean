-- Prove2me | solution 1 for GlobalTheory.exists_polyContent_eq
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:51:55.210442+00:00
-- url     : https://prove2.me/submissions/29f3c96f-00c0-49ab-b022-49f9cb4d436d

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
theorem _root_.solution (c : (σ →₀ ℕ) →₀ M) :
    ∃ m, polyContent v b c = basisVal v b (c m) := by
  first
    | (by_cases hc : c = 0
       · refine ⟨0, ?_⟩
         subst hc
         unfold GlobalTheory.polyContent
         rw [GlobalTheory.coeffSup_zero]
         simp [GlobalTheory.basisVal]
       · obtain ⟨m, _, hm⟩ := GlobalTheory.exists_mem_support_coeffSup_eq (N := GlobalTheory.basisVal v b) hc
         exact ⟨m, hm⟩)

