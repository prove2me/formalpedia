-- Prove2me | solution 2 for GlobalTheory.isGreatest_basisVal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:39:44.283987+00:00
-- url     : https://prove2.me/submissions/2d5095dc-a89c-4746-a409-7d75dd1609af

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TensorContentEqPolyContentScalarCoeffs
import Theorems.Thm_GlobalTheory_le_basisVal
import Theorems.Thm_GlobalTheory_exists_basisVal_eq
import Theorems.Thm_GlobalTheory_valuation_linearMap_le_basisVal

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
theorem _root_.solution (x : M) :
    IsGreatest {γ | ∃ φ : M →ₗ[R] R, (∀ y, basisVal v b y ≤ 1 → v (φ y) ≤ 1) ∧ v (φ x) = γ}
      (basisVal v b x) := by
  constructor
  · by_cases hx : x = 0
    · exact ⟨0, by simp, by simp [hx]⟩
    · obtain ⟨i, hi⟩ := exists_basisVal_eq v b hx
      exact ⟨b.coord i, fun y hy => (le_basisVal v b y i).trans hy, hi.symm⟩
  · rintro _ ⟨φ, hφ, rfl⟩
    exact valuation_linearMap_le_basisVal v b φ (fun i => hφ _ (by simp)) x
end GlobalTheory
