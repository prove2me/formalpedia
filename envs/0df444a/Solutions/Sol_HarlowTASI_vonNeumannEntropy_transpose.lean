-- Prove2me | solution 1 for HarlowTASI.vonNeumannEntropy_transpose
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:51:39.002453+00:00
-- url     : https://prove2.me/submissions/8f24cd03-2ab5-4a23-9e23-8a357c6c5bc2

import Mathlib
import Definitions.Def_HarlowTASI_QuantumBasics
open Matrix Polynomial
open scoped Kronecker ComplexOrder

namespace S192HT

lemma ent_roots {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    HarlowTASI.vonNeumannEntropy A =
      ((A.charpoly.roots).map (fun z : ℂ => Real.negMulLog z.re)).sum := by
  rw [hA.roots_charpoly_eq_eigenvalues, Multiset.map_map]
  unfold HarlowTASI.vonNeumannEntropy
  rw [dif_pos hA]
  rfl

lemma ent_transpose {n : Type} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) : HarlowTASI.vonNeumannEntropy Hᵀ = HarlowTASI.vonNeumannEntropy H := by
  by_cases hH : H.IsHermitian
  · have hT : Hᵀ.IsHermitian := hH.transpose
    rw [ent_roots _ hT, ent_roots _ hH, charpoly_transpose]
  · have hT : ¬ Hᵀ.IsHermitian := fun h => hH (by simpa using h.transpose)
    unfold HarlowTASI.vonNeumannEntropy
    rw [dif_neg hT, dif_neg hH]

lemma card_le_of_iso {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (W : Matrix m n ℂ) (hW : Wᴴ * W = 1) : Fintype.card n ≤ Fintype.card m := by
  have h1 : (Wᴴ * W).rank = Fintype.card n := by rw [hW, rank_one]
  have h2 := rank_mul_le_right Wᴴ W
  have h3 := rank_le_card_height W
  omega

lemma ent_iso {m n : Type} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] (W : Matrix m n ℂ) (hW : HarlowTASI.IsIsometry W) (Y : Matrix n n ℂ) :
    HarlowTASI.vonNeumannEntropy (W * Y * Wᴴ) = HarlowTASI.vonNeumannEntropy Y := by
  have hW' : Wᴴ * W = 1 := hW
  by_cases hY : Y.IsHermitian
  · have hZ : (W * Y * Wᴴ).IsHermitian := isHermitian_mul_mul_conjTranspose W hY
    rw [ent_roots _ hZ, ent_roots _ hY]
    have hc : (W * Y * Wᴴ).charpoly =
        X ^ (Fintype.card m - Fintype.card n) * Y.charpoly := by
      rw [Matrix.mul_assoc, charpoly_mul_comm_of_le _ _ (card_le_of_iso W hW'), Matrix.mul_assoc, hW',
        Matrix.mul_one]
    rw [hc, roots_mul (mul_ne_zero (pow_ne_zero _ X_ne_zero) (charpoly_monic Y).ne_zero),
      roots_X_pow, Multiset.map_add, Multiset.sum_add]
    simp [Multiset.map_nsmul, Multiset.sum_nsmul]
  · have hZ : ¬ (W * Y * Wᴴ).IsHermitian := by
      intro h
      apply hY
      have := isHermitian_conjTranspose_mul_mul W h
      have e : Wᴴ * (W * Y * Wᴴ) * W = Y := by
        rw [show Wᴴ * (W * Y * Wᴴ) * W = (Wᴴ * W) * Y * (Wᴴ * W) by simp [Matrix.mul_assoc], hW']
        simp
      rwa [e] at this
    unfold HarlowTASI.vonNeumannEntropy
    rw [dif_neg hZ, dif_neg hY]

end S192HT

open HarlowTASI in
theorem solution {n : Type} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) : vonNeumannEntropy Hᵀ = vonNeumannEntropy H := S192HT.ent_transpose H
