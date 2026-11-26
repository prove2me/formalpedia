-- Prove2me | solution 1 for GlobalTheory.polyContent_eq_of_le_one
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T14:00:23.119926+00:00
-- url     : https://prove2.me/submissions/dbbdc950-65ac-44b1-ab75-c5a3e99f2257

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

theorem solution (b' : Basis κ R M) (h : ∀ i, basisVal v b' (b i) ≤ 1)
    (h' : ∀ j, basisVal v b (b' j) ≤ 1) (c : (σ →₀ ℕ) →₀ M) :
    polyContent v b c = polyContent v b' c := by
  have heq (x : M) : basisVal v b x = basisVal v b' x := by
    refine le_antisymm ?_ ?_
    · rw [basisVal_le_iff]
      intro i
      have : b.repr x i =
          ∑ j ∈ (b'.repr x).support, b'.repr x j * b.repr (b' j) i := by
        conv_lhs => rw [← b'.linearCombination_repr x]
        rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, Finsupp.finsetSum_apply]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
      rw [this]
      refine v.map_sum_le fun j _ => ?_
      rw [v.map_mul]
      have h1 : v (b.repr (b' j) i) ≤ 1 := (basisVal_le_iff v b).mp (h' j) i
      have h2 : v (b'.repr x j) ≤ basisVal v b' x := (basisVal_le_iff v b').mp le_rfl j
      exact (mul_le_mul' h2 h1).trans_eq (mul_one _)
    · rw [basisVal_le_iff]
      intro j
      have : b'.repr x j =
          ∑ i ∈ (b.repr x).support, b.repr x i * b'.repr (b i) j := by
        conv_lhs => rw [← b.linearCombination_repr x]
        rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, Finsupp.finsetSum_apply]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
      rw [this]
      refine v.map_sum_le fun i _ => ?_
      rw [v.map_mul]
      have h1 : v (b'.repr (b i) j) ≤ 1 := (basisVal_le_iff v b').mp (h i) j
      have h2 : v (b.repr x i) ≤ basisVal v b x := (basisVal_le_iff v b).mp le_rfl i
      exact (mul_le_mul' h2 h1).trans_eq (mul_one _)
  unfold polyContent
  refine le_antisymm ?_ ?_
  · rw [coeffSup_le_iff (basisVal_zero v b)]
    intro m
    rw [heq]
    exact le_coeffSup (basisVal_zero v b') c m
  · rw [coeffSup_le_iff (basisVal_zero v b')]
    intro m
    rw [← heq]
    exact le_coeffSup (basisVal_zero v b) c m
