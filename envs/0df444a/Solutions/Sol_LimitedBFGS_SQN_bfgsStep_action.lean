-- Prove2me | solution 1 for LimitedBFGS.SQN.bfgsStep_action
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-30T05:41:17.194543+00:00
-- url     : https://prove2.me/submissions/5dde7fd5-1671-48ef-b337-76d4040a52d3

import Mathlib
import Definitions.Def_LimitedBFGS_SQN_specialH

open Matrix
open LimitedBFGS.SQN

theorem solution {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (s y g : Fin n → ℝ)
    (hs : s ⬝ᵥ g = 0) (hy : y ⬝ᵥ (H *ᵥ g) = 0) :
    bfgsStep H s y *ᵥ g = H *ᵥ g ∧
      bfgsStep H s y *ᵥ g = H *ᵥ g - (bfgsRho s y * (y ⬝ᵥ (H *ᵥ g))) • s := by
  have hop : ∀ (c : ℝ) (v : Fin n → ℝ), MulOpposite.op c • v = c • v :=
    fun c v => by simp
  have hVg : bfgsV s y *ᵥ g = g := by
    rw [bfgsV, sub_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec, hop,
      hs, zero_smul, smul_zero, sub_zero]
  have hVtHg : (bfgsV s y)ᵀ *ᵥ (H *ᵥ g) = H *ᵥ g := by
    rw [bfgsV, transpose_sub, transpose_one, transpose_smul, transpose_vecMulVec,
      sub_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec, hop, hy,
      zero_smul, smul_zero, sub_zero]
  have key : bfgsStep H s y *ᵥ g = H *ᵥ g - (bfgsRho s y * (y ⬝ᵥ (H *ᵥ g))) • s := by
    rw [bfgsStep, add_mulVec, ← mulVec_mulVec, ← mulVec_mulVec]
    rw [hVg, smul_mulVec, vecMulVec_mulVec, hop, hs, zero_smul, smul_zero, add_zero]
    rw [bfgsV, transpose_sub, transpose_one, transpose_smul, transpose_vecMulVec,
      sub_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec, hop, smul_smul]
  exact ⟨by rw [key, hy, mul_zero, zero_smul, sub_zero], key⟩
