-- Prove2me | solution 1 for GlobalTheory.valuation_linearMap_le_basisVal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:42:19.338922+00:00
-- url     : https://prove2.me/submissions/506e511b-6728-4a4e-b9ed-14fbddc1cd3b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TensorContentEqPolyContentScalarCoeffs
import Theorems.Thm_GlobalTheory_le_basisVal

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
theorem _root_.solution (φ : M →ₗ[R] R) (h : ∀ i, v (φ (b i)) ≤ 1) (x : M) :
    v (φ x) ≤ basisVal v b x := by
  conv_lhs => rw [← b.linearCombination_repr x, Finsupp.linearCombination_apply, Finsupp.sum,
    map_sum]
  refine v.map_sum_le fun i _ => ?_
  rw [map_smul, smul_eq_mul, map_mul]
  exact (mul_le_mul' (le_basisVal v b x i) (h i)).trans_eq (mul_one _)
end GlobalTheory
