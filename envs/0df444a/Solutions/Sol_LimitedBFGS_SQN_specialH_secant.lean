-- Prove2me | solution 1 for LimitedBFGS.SQN.specialH_secant
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-28T04:22:32.493897+00:00
-- url     : https://prove2.me/submissions/cac06018-947a-44eb-8e8e-ff52f06da427

import Mathlib
import Definitions.Def_LimitedBFGS_SQN_specialH

open Matrix

namespace LimitedBFGS.SQN

/-- Eq. (3) in one step: `vecMulVec u v *ᵥ w = (v ⬝ᵥ w) • u`. -/
theorem vecMulVec_mulVec_eq {n : ℕ} (u v w : Fin n → ℝ) :
    vecMulVec u v *ᵥ w = (v ⬝ᵥ w) • u := by
  simpa using Matrix.vecMulVec_mulVec u v w

/-- Eq. (7) in matrix form: `vᵀ w = w − ρ (yᵀw) s`, since `v = I − ρ y sᵀ`. -/
theorem bfgsV_transpose_mulVec {n : ℕ} (s y w : Fin n → ℝ) :
    (bfgsV s y)ᵀ *ᵥ w = w - (bfgsRho s y * (y ⬝ᵥ w)) • s := by
  have htr : (bfgsV s y)ᵀ = 1 - bfgsRho s y • vecMulVec s y := by
    simp [bfgsV, transpose_smul, transpose_sub, transpose_one, transpose_vecMulVec]
  rw [htr, sub_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec_eq]
  funext k
  simp only [Pi.smul_apply, sub_eq_add_neg, smul_neg]
  rw [smul_smul, mul_comm]

/-- `ρ (yᵀs) s = s` when `yᵀs ≠ 0`: the rank-one term of eq. (3) on `y`. -/
theorem rho_smul {n : ℕ} (s y : Fin n → ℝ) (hys : y ⬝ᵥ s ≠ 0) :
    (bfgsRho s y * (y ⬝ᵥ s)) • s = s := by
  funext k
  simp only [Pi.smul_apply]
  rw [bfgsRho, div_eq_mul_inv, one_mul, inv_mul_cancel₀ hys, one_smul]

/-- `ρ (yᵀs) y = y` when `yᵀs ≠ 0`, the companion identity on `y` itself. -/
theorem rho_smul_y {n : ℕ} (s y : Fin n → ℝ) (hys : y ⬝ᵥ s ≠ 0) :
    (bfgsRho s y * (y ⬝ᵥ s)) • y = y := by
  funext k
  simp only [Pi.smul_apply]
  rw [bfgsRho, div_eq_mul_inv, one_mul, inv_mul_cancel₀ hys, one_smul]

/-- Eq. (7), first identity: `v y = 0` whenever `yᵀs ≠ 0`. -/
theorem bfgsV_mulVec_y {n : ℕ} (s y : Fin n → ℝ) (hys : y ⬝ᵥ s ≠ 0) :
    bfgsV s y *ᵥ y = 0 := by
  rw [bfgsV, sub_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec_eq,
    dotProduct_comm]
  rw [smul_smul, rho_smul_y s y hys, sub_self]

/-- Eq. (7), second identity: `v a = a` whenever `sᵀa = 0`. -/
theorem bfgsV_mulVec_of_orth {n : ℕ} (s y a : Fin n → ℝ) (h : s ⬝ᵥ a = 0) :
    bfgsV s y *ᵥ a = a := by
  rw [bfgsV, sub_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec_eq, h]
  simp

/-- A BFGS update satisfies its own new secant equation for any `H`. -/
theorem bfgsStep_mulVec_y {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (s y : Fin n → ℝ)
    (hys : y ⬝ᵥ s ≠ 0) : bfgsStep H s y *ᵥ y = s := by
  have hv : bfgsV s y *ᵥ y = 0 := bfgsV_mulVec_y s y hys
  rw [bfgsStep, add_mulVec, smul_mulVec, vecMulVec_mulVec_eq, dotProduct_comm,
    smul_smul, ← mulVec_mulVec, hv, mulVec_zero, zero_add]
  exact rho_smul s y hys

/-- Over `ℝ`, a positive definite `A` is symmetric, so `(A sᵢ)ᵀ sⱼ = sᵢᵀ A sⱼ`:
conjugacy may be read with the two indices exchanged. -/
theorem posDef_conj_comm {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    (p q : Fin n → ℝ) : (A *ᵥ p) ⬝ᵥ q = p ⬝ᵥ (A *ᵥ q) := by
  have hsym : Aᵀ = A := by simpa using hA.1.eq
  calc (A *ᵥ p) ⬝ᵥ q = q ⬝ᵥ A *ᵥ p := dotProduct_comm _ _
    _ = q ⬝ᵥ Aᵀ *ᵥ p := by rw [hsym]
    _ = p ⬝ᵥ A *ᵥ q := dotProduct_transpose_mulVec A q p

/-- A BFGS update preserves the secant equation of an earlier conjugate index. -/
theorem bfgsStep_preserves {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ)
    (si yi yj sj : Fin n → ℝ) (hH : H *ᵥ yj = sj) (hysi : yi ⬝ᵥ si ≠ 0)
    (hs_yj : si ⬝ᵥ yj = 0) (hyi_sj : yi ⬝ᵥ sj = 0) :
    bfgsStep H si yi *ᵥ yj = sj := by
  have hva : bfgsV si yi *ᵥ yj = yj := bfgsV_mulVec_of_orth si yi yj hs_yj
  have hvt : (bfgsV si yi)ᵀ *ᵥ sj = sj := by
    rw [bfgsV_transpose_mulVec, hyi_sj]
    simp
  rw [bfgsStep, add_mulVec, smul_mulVec, vecMulVec_mulVec_eq,
    ← mulVec_mulVec, hva, ← mulVec_mulVec, hH, hvt, hs_yj]
  simp

/-- **The fold invariant**: folding the BFGS step over the pairs with indices
`a, …, a+t−1` leaves `H *ᵥ y j = s j` for every `j` in the window `a ≤ j < a+t`. -/
theorem fold_secant {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    {s y : ℕ → Fin n → ℝ} {k₀ : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (a t : ℕ)
    (hstep : ∀ p, a ≤ p → p < k₀ → y p ⬝ᵥ s p ≠ 0)
    (hconj : ∀ p q, p < k₀ → q < k₀ → p ≠ q → s p ⬝ᵥ (A *ᵥ s q) = 0)
    (hy : ∀ q, y q = A *ᵥ s q)
    (hwin : a + t ≤ k₀) :
    (∀ j, a ≤ j → j < a + t →
      ((List.range t).map fun i => (s (a + i), y (a + i))).foldl
          (fun H p => bfgsStep H p.1 p.2) H *ᵥ y j = s j) := by
  classical
  induction t generalizing H with
  | zero =>
      intro j hj _
      omega
  | succ t ih =>
      intro j hj₁ hj₂
      -- `range (t+1) = range t ++ [t]`: the old fold, then one more step.
      rw [List.range_succ, List.map_append, List.map_singleton, List.foldl_append]
      by_cases hjeq : j = a + t
      · -- newest index: the update's own secant equation
        subst hjeq
        simpa using bfgsStep_mulVec_y
          (((List.range t).map fun i => (s (a + i), y (a + i))).foldl
            (fun H p => bfgsStep H p.1 p.2) H)
          (s (a + t)) (y (a + t)) (hstep (a + t) (by omega) (by omega))
      · -- an earlier index: the new step preserves its secant
        have hjlt : j < a + t := by omega
        have hprev : ((List.range t).map fun i => (s (a + i), y (a + i))).foldl
            (fun H p => bfgsStep H p.1 p.2) H *ᵥ y j = s j :=
          ih H (by omega) j hj₁ hjlt
        refine bfgsStep_preserves _ (s (a + t)) (y (a + t)) (y j) (s j) hprev
          (hstep (a + t) (by omega) (by omega)) ?_ ?_
        · -- `sᵢᵀ yⱼ = 0` by conjugacy
          simpa [hy j] using hconj (a + t) j (by omega) (by omega) (by omega)
        · -- `yᵢᵀ sⱼ = 0` by symmetry of `A`
          calc y (a + t) ⬝ᵥ s j = (A *ᵥ s (a + t)) ⬝ᵥ s j := by rw [hy (a + t)]
            _ = s (a + t) ⬝ᵥ (A *ᵥ s j) := posDef_conj_comm hA _ _
            _ = 0 := hconj (a + t) j (by omega) (by omega) (by omega)

end LimitedBFGS.SQN

open LimitedBFGS.SQN

/-- Property (b), eq. (6), pp. 775–776: `H_k y_j = s_j` for `j = k−1, …, k−m`
whenever `k > m`. -/
theorem solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (H₀ : Matrix (Fin n) (Fin n) ℝ) (hH₀ : H₀.PosDef) (m : ℕ) (hm : 1 ≤ m)
    (s y : ℕ → Fin n → ℝ) (k : ℕ) (hk : m < k) (hy : ∀ j, y j = A *ᵥ s j)
    (hconj : ∀ i j, i < k → j < k → i ≠ j → s i ⬝ᵥ (A *ᵥ s j) = 0)
    (hys : ∀ i, i < k → 0 < y i ⬝ᵥ s i) (j : ℕ) (hj₁ : k - m ≤ j) (hj₂ : j < k) :
    specialH H₀ m s y k *ᵥ y j = s j := by
  -- `k > m` forces `min k m = m`, so `specialH` folds exactly the window
  -- `k − m, …, k − 1` and `j` is one of the indices it must satisfy.
  have hmin : min k m = m := Nat.min_eq_right (Nat.le_of_lt hk)
  rw [specialH, hmin]
  refine fold_secant hA H₀ (k - m) m (fun p _ _ => ne_of_gt (hys p (by omega)))
    (fun p q _ _ hne => hconj p q (by omega) (by omega) hne) hy (by omega) j hj₁ ?_
  omega
