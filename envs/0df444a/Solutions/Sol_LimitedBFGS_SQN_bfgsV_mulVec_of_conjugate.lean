-- Prove2me | solution 1 for LimitedBFGS.SQN.bfgsV_mulVec_of_conjugate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-27T22:05:57.348607+00:00
-- url     : https://prove2.me/submissions/fcf2b291-ead8-4e0a-92dd-f96563b96fc0

import Mathlib
import Definitions.Def_LimitedBFGS_SQN_bfgsStep

open Matrix

namespace LimitedBFGS.SQN

/-- The rank-one product `(u vᵀ) *ᵥ w` is `u • (vᵀw)`, entrywise. This is the
`vecMulVec_mulVec` computation, proved directly so that the scalar `v ⬝ᵥ w`
comes out in the order the BFGS correction needs. -/
theorem vecMulVec_mulVec_apply {n : ℕ} (u v w : Fin n → ℝ) (k : Fin n) :
    (vecMulVec u v *ᵥ w) k = u k * (v ⬝ᵥ w) := by
  simp [mulVec, dotProduct, vecMulVec, Finset.mul_sum, mul_left_comm, mul_comm]

/-- The action of `v_i = I − ρ_i y_i s_iᵀ` on a vector `w`: the correction term is
`(1 / yᵀs) • ((sᵀw) • y)`, so `v_i w = w − ρ_i (s_iᵀ w) y_i`. -/
theorem bfgsV_mulVec_formula {n : ℕ} (s y w : Fin n → ℝ) :
    bfgsV s y *ᵥ w = w - (1 / (y ⬝ᵥ s)) • ((s ⬝ᵥ w) • y) := by
  classical
  have hstep : bfgsV s y *ᵥ w = w - bfgsRho s y • (vecMulVec y s *ᵥ w) := by
    rw [bfgsV, sub_mulVec, one_mulVec, smul_mulVec]
  have hcorr : bfgsRho s y • (vecMulVec y s *ᵥ w) = (1 / (y ⬝ᵥ s)) • ((s ⬝ᵥ w) • y) := by
    have key : vecMulVec y s *ᵥ w = fun k => y k * (s ⬝ᵥ w) := by
      funext k
      exact vecMulVec_mulVec_apply y s w k
    rw [bfgsRho, key]
    funext k
    simp [smul_eq_mul, mul_comm]
  rw [hstep, hcorr]

theorem conj_two_families {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (s y : ℕ → Fin n → ℝ) (N : ℕ) (hy : ∀ j, y j = A *ᵥ s j)
    (hconj : ∀ i j, i < N → j < N → i ≠ j → s i ⬝ᵥ (A *ᵥ s j) = 0)
    (hys : ∀ i, i < N → 0 < y i ⬝ᵥ s i) :
    (∀ i, i < N → bfgsV (s i) (y i) *ᵥ y i = 0) ∧
      (∀ i j, j < i → i < N → bfgsV (s i) (y i) *ᵥ y j = y j) := by
  refine ⟨?_, ?_⟩
  · intro i hi
    rw [bfgsV_mulVec_formula, dotProduct_comm]
    have hd : s i ⬝ᵥ y i ≠ 0 := by
      rw [dotProduct_comm]
      exact ne_of_gt (hys i hi)
    have hc : (1 / (s i ⬝ᵥ y i)) * (s i ⬝ᵥ y i) = 1 := div_mul_cancel₀ _ hd
    have hcorr : (1 / (s i ⬝ᵥ y i)) • ((s i ⬝ᵥ y i) • y i) = y i := by
      rw [smul_smul, hc, one_smul]
    rw [hcorr, sub_self]
  · intro i j hji hi
    rw [bfgsV_mulVec_formula, dotProduct_comm]
    have h1 : s i ⬝ᵥ y j = 0 := by
      rw [hy j]
      exact hconj i j hi (Nat.lt_trans hji hi) (Ne.symm (Nat.ne_of_lt hji))
    rw [h1, zero_smul, smul_zero, sub_zero]

end LimitedBFGS.SQN

open LimitedBFGS.SQN

/-- `theorem solution` is the required top-level declaration. -/
theorem solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (s y : ℕ → Fin n → ℝ) (N : ℕ) (hy : ∀ j, y j = A *ᵥ s j)
    (hconj : ∀ i j, i < N → j < N → i ≠ j → s i ⬝ᵥ (A *ᵥ s j) = 0)
    (hys : ∀ i, i < N → 0 < y i ⬝ᵥ s i) :
    (∀ i, i < N → bfgsV (s i) (y i) *ᵥ y i = 0) ∧
      (∀ i j, j < i → i < N → bfgsV (s i) (y i) *ᵥ y j = y j) :=
  conj_two_families A hA s y N hy hconj hys
