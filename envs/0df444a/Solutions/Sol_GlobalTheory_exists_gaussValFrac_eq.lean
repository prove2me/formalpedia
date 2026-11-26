-- Prove2me | solution 1 for GlobalTheory.exists_gaussValFrac_eq
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T12:57:28.496089+00:00
-- url     : https://prove2.me/submissions/6b8b1fa1-d3c1-43f4-be42-4e0ac489e18f

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

private lemma exists_gaussVal_eq (f : MvPolynomial σ K) : ∃ c : K, gaussVal v f = v c := by
  by_cases hf : f = 0
  · refine ⟨0, ?_⟩
    simp [hf]
  · have hc : AddMonoidAlgebra.coeff f ≠ 0 :=
      AddMonoidAlgebra.coeff_eq_zero.not.mpr hf
    obtain ⟨m, -, hm⟩ := exists_mem_support_coeffSup_eq (N := v) hc
    refine ⟨coeff m f, ?_⟩
    simpa [gaussVal, gaussValAlg, MvPolynomial.coeff] using hm

theorem solution (x : F) : ∃ c : K, gaussValFrac v σ F x = v c := by
  obtain ⟨f, g, rfl⟩ := IsLocalization.exists_mk'_eq (nonZeroDivisors (MvPolynomial σ K)) x
  rw [IsFractionRing.mk'_eq_div, Valuation.map_div, gaussValFrac_algebraMap,
    gaussValFrac_algebraMap]
  obtain ⟨a, ha⟩ := exists_gaussVal_eq v f
  obtain ⟨b, hb⟩ := exists_gaussVal_eq v (g : MvPolynomial σ K)
  refine ⟨a / b, ?_⟩
  rw [ha, hb, Valuation.map_div]
