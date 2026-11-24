-- Prove2me | solution 1 for GlobalTheory.exists_eq_C_mul_gaussVal_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:00:03.38717+00:00
-- url     : https://prove2.me/submissions/6ac6f02f-b555-45ae-bf61-28a3c4a5c876

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TensorContentEqPolyContentScalarCoeffs
import Theorems.Thm_GlobalTheory_exists_gaussVal_eq

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
variable [LinearOrderedCommMonoidWithZero Γ₀] [Nontrivial Γ₀] (v : Valuation K Γ₀)
namespace GlobalTheory
theorem _root_.solution {f : MvPolynomial σ K} (hf : f ≠ 0) :
    ∃ (c : K) (g : MvPolynomial σ K), c ≠ 0 ∧ v c = gaussVal v f ∧ gaussVal v g = 1 ∧
      f = C c * g := by
  obtain ⟨m, hm⟩ := exists_gaussVal_eq v f
  have hc : coeff m f ≠ 0 := fun h => hf ((gaussVal_eq_zero_iff v).mp (by rw [hm, h, map_zero]))
  refine ⟨coeff m f, C (coeff m f)⁻¹ * f, hc, hm.symm, ?_, ?_⟩
  · rw [map_mul, gaussVal_C, hm, ← map_mul, inv_mul_cancel₀ hc, map_one]
  · rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ hc, C_1, one_mul]
end GlobalTheory
