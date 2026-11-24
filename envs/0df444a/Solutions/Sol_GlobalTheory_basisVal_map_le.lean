-- Prove2me | solution 1 for GlobalTheory.basisVal_map_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:34:00.936429+00:00
-- url     : https://prove2.me/submissions/4d3a9bbe-bc89-48aa-961c-0afe047e229f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TensorContentEqPolyContentScalarCoeffs
import Theorems.Thm_GlobalTheory_le_basisVal
import Theorems.Thm_GlobalTheory_basisVal_sum_le

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
theorem _root_.solution (c : Basis κ R N) (φ : M →ₗ[R] N) (h : ∀ i, basisVal v c (φ (b i)) ≤ 1)
    (x : M) : basisVal v c (φ x) ≤ basisVal v b x := by
  conv_lhs => rw [← b.linearCombination_repr x, Finsupp.linearCombination_apply, Finsupp.sum,
    map_sum]
  refine basisVal_sum_le v c fun i _ => ?_
  rw [map_smul, basisVal_smul]
  exact (mul_le_mul' (le_basisVal v b x i) (h i)).trans_eq (mul_one _)
end GlobalTheory
