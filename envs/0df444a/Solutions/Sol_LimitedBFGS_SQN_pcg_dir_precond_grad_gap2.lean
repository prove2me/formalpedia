-- Prove2me | solution 1 for LimitedBFGS.SQN.pcg_dir_precond_grad_gap2
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-30T05:47:41.479858+00:00
-- url     : https://prove2.me/submissions/750fd890-7ad0-4123-bf51-7f331706bf7f

import Mathlib
import Definitions.Def_LimitedBFGS_SQN_pcgIter
import Theorems.Thm_LimitedBFGS_SQN_pcg_joint_prefix_invariants

open Matrix
open LimitedBFGS.SQN

theorem solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (b : Fin n → ℝ) (H₀ : Matrix (Fin n) (Fin n) ℝ) (hH₀ : H₀.PosDef) (x₀ : Fin n → ℝ) :
    ∀ p q : ℕ, p + 2 ≤ q →
      (pcgIter A b H₀ x₀ p).d ⬝ᵥ (A *ᵥ (H₀ *ᵥ grad A b (pcgIter A b H₀ x₀ q).x)) = 0 := by
  intro p q hpq
  have hJ := pcg_joint_prefix_invariants A hA b H₀ hH₀ x₀
  have hsym : Aᵀ = A := by simpa using hA.isHermitian.eq
  have hswap : ∀ u v : Fin n → ℝ, u ⬝ᵥ (A *ᵥ v) = v ⬝ᵥ (A *ᵥ u) := by
    intro u v
    calc u ⬝ᵥ (A *ᵥ v) = u ⬝ᵥ (Aᵀ *ᵥ v) := by rw [hsym]
      _ = v ⬝ᵥ (A *ᵥ u) := dotProduct_transpose_mulVec A u v
  cases q with
  | zero => omega
  | succ k =>
    have hpk : p < k := by omega
    have hpk1 : p < k + 1 := by omega
    have hconj_k : (pcgIter A b H₀ x₀ p).d ⬝ᵥ (A *ᵥ (pcgIter A b H₀ x₀ k).d) = 0 := by
      rw [hswap]
      exact (hJ k).2.2 p hpk
    have hconj_k1 : (pcgIter A b H₀ x₀ p).d
        ⬝ᵥ (A *ᵥ (pcgIter A b H₀ x₀ (k + 1)).d) = 0 := by
      rw [hswap]
      exact (hJ (k + 1)).2.2 p hpk1
    have hcoupl : (pcgIter A b H₀ x₀ p).d ⬝ᵥ (A *ᵥ (pcgIter A b H₀ x₀ (k + 1)).d)
        = -((pcgIter A b H₀ x₀ p).d
            ⬝ᵥ (A *ᵥ (H₀ *ᵥ grad A b (pcgIter A b H₀ x₀ (k + 1)).x)))
          + ((grad A b (pcgIter A b H₀ x₀ (k + 1)).x
                - grad A b (pcgIter A b H₀ x₀ k).x)
              ⬝ᵥ (H₀ *ᵥ grad A b (pcgIter A b H₀ x₀ (k + 1)).x))
            / ((grad A b (pcgIter A b H₀ x₀ (k + 1)).x
                - grad A b (pcgIter A b H₀ x₀ k).x)
              ⬝ᵥ (pcgIter A b H₀ x₀ k).d)
            * ((pcgIter A b H₀ x₀ p).d ⬝ᵥ (A *ᵥ (pcgIter A b H₀ x₀ k).d)) := by
      simp only [pcgIter, mulVec_add, mulVec_neg, mulVec_smul, dotProduct_add, dotProduct_neg,
        dotProduct_smul, smul_eq_mul]
    have hEq := hcoupl
    rw [hconj_k1] at hEq
    rw [hconj_k] at hEq
    simp only [mul_zero, add_zero] at hEq
    exact neg_eq_zero.mp hEq.symm
