-- Prove2me | solution 1 for GlobalTheory.isGreatest_basisVal
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T14:02:03.689211+00:00
-- url     : https://prove2.me/submissions/b2afbd78-7dee-4e27-907b-bacc1ab63021

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

theorem solution (x : M) :
    IsGreatest {γ | ∃ φ : M →ₗ[R] R, (∀ y, basisVal v b y ≤ 1 → v (φ y) ≤ 1) ∧ v (φ x) = γ}
      (basisVal v b x) := by
  refine ⟨?mem, ?max⟩
  · by_cases hx : b.repr x = 0
    · have hx0 : x = 0 := b.repr.map_eq_zero_iff.mp hx
      refine ⟨0, ?_, ?_⟩
      · intro y hy
        simp
      · simp [hx0, basisVal_zero]
    · obtain ⟨i, -, hi⟩ := exists_mem_support_coeffSup_eq (N := (v : R → Γ₀)) hx
      refine ⟨b.coord i, ?_, ?_⟩
      · intro y hy
        rw [Basis.coord_apply]
        exact (le_coeffSup v.map_zero (b.repr y) i).trans hy
      · rw [Basis.coord_apply, basisVal, hi]
  · intro γ hγ
    obtain ⟨φ, hφ, rfl⟩ := hγ
    have : φ x = ∑ i ∈ (b.repr x).support, b.repr x i * φ (b i) := by
      conv_lhs => rw [← b.linearCombination_repr x]
      rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, smul_eq_mul]
    rw [this]
    refine v.map_sum_le fun i _ => ?_
    rw [v.map_mul]
    have h1 : v (φ (b i)) ≤ 1 := hφ (b i) (by simp [basisVal_basis])
    have h2 : v (b.repr x i) ≤ basisVal v b x := (basisVal_le_iff v b).mp le_rfl i
    exact (mul_le_mul' h2 h1).trans_eq (mul_one _)
