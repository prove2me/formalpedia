-- Prove2me | solution 1 for LimitedBFGS.SQN.pcg_step_coefficient
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-30T05:45:40.243725+00:00
-- url     : https://prove2.me/submissions/e31b74df-7ace-4a3d-b37c-283cd64add83

import Mathlib
import Definitions.Def_LimitedBFGS_SQN_pcgIter
import Theorems.Thm_LimitedBFGS_SQN_pcg_grad_orthogonality
import Theorems.Thm_LimitedBFGS_SQN_pcg_orthogonality

open Matrix
open LimitedBFGS.SQN

theorem solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (b : Fin n → ℝ) (H₀ : Matrix (Fin n) (Fin n) ℝ) (hH₀ : H₀.PosDef) (x₀ : Fin n → ℝ)
    (m : ℕ) :
    (let gm := grad A b (pcgIter A b H₀ x₀ m).x
     let dm := (pcgIter A b H₀ x₀ m).d
     let gm1 := grad A b (pcgIter A b H₀ x₀ (m + 1)).x
     let ym := gm1 - gm
     let beta := (ym ⬝ᵥ (H₀ *ᵥ gm1)) / (ym ⬝ᵥ dm)
     (gm1 ⬝ᵥ dm = 0) ∧
       ((gm ⬝ᵥ (H₀ *ᵥ gm)) ≠ 0 →
         beta = (gm1 ⬝ᵥ (H₀ *ᵥ gm1)) / (gm ⬝ᵥ (H₀ *ᵥ gm)))) := by
  have horth := pcg_orthogonality A hA b H₀ hH₀ x₀
  have hgo := pcg_grad_orthogonality A hA b H₀ hH₀ x₀
  dsimp only
  refine ⟨horth.2 (m + 1) m (Nat.lt_succ_self m), ?_⟩
  intro ha
  have hcross : grad A b (pcgIter A b H₀ x₀ m).x
      ⬝ᵥ (H₀ *ᵥ grad A b (pcgIter A b H₀ x₀ (m + 1)).x) = 0 :=
    hgo m (m + 1) (by omega)
  have hgm_dm : grad A b (pcgIter A b H₀ x₀ m).x ⬝ᵥ (pcgIter A b H₀ x₀ m).d
      = -(grad A b (pcgIter A b H₀ x₀ m).x
          ⬝ᵥ (H₀ *ᵥ grad A b (pcgIter A b H₀ x₀ m).x)) := by
    cases m with
    | zero =>
      simp only [pcgIter, dotProduct_neg]
    | succ k =>
      have h0 : grad A b (pcgIter A b H₀ x₀ (k + 1)).x
          ⬝ᵥ (pcgIter A b H₀ x₀ k).d = 0 :=
        horth.2 (k + 1) k (Nat.lt_succ_self k)
      have h0' : grad A b ((pcgIter A b H₀ x₀ k).x
            + exactStep A b (pcgIter A b H₀ x₀ k).x (pcgIter A b H₀ x₀ k).d
              • (pcgIter A b H₀ x₀ k).d)
          ⬝ᵥ (pcgIter A b H₀ x₀ k).d = 0 := by
        simpa only [pcgIter] using h0
      simp only [pcgIter, dotProduct_add, dotProduct_neg, dotProduct_smul, smul_eq_mul]
      rw [h0', mul_zero, add_zero]
  have hnum : (grad A b (pcgIter A b H₀ x₀ (m + 1)).x
        - grad A b (pcgIter A b H₀ x₀ m).x)
      ⬝ᵥ (H₀ *ᵥ grad A b (pcgIter A b H₀ x₀ (m + 1)).x)
      = grad A b (pcgIter A b H₀ x₀ (m + 1)).x
        ⬝ᵥ (H₀ *ᵥ grad A b (pcgIter A b H₀ x₀ (m + 1)).x) := by
    rw [sub_dotProduct, hcross, sub_zero]
  have hden : (grad A b (pcgIter A b H₀ x₀ (m + 1)).x
        - grad A b (pcgIter A b H₀ x₀ m).x)
      ⬝ᵥ (pcgIter A b H₀ x₀ m).d
      = grad A b (pcgIter A b H₀ x₀ m).x
        ⬝ᵥ (H₀ *ᵥ grad A b (pcgIter A b H₀ x₀ m).x) := by
    rw [sub_dotProduct, horth.2 (m + 1) m (Nat.lt_succ_self m), zero_sub, hgm_dm, neg_neg]
  rw [hnum, hden]
