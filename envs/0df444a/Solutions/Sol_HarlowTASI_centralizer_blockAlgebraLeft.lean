-- Prove2me | solution 1 for HarlowTASI.centralizer_blockAlgebraLeft
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-10T15:21:14.839243+00:00
-- url     : https://prove2.me/submissions/3e44adf0-a377-4186-9b1a-89ac6d8f1fdb

import Mathlib
import Definitions.Def_HarlowTASI_OperatorAlgebras

namespace HarlowTASI
open Matrix
open scoped Kronecker

variable {N : ℕ} {dr drb : Fin N → ℕ}

lemma cbl_left_mul_apply (x : ∀ a, Matrix (Fin (dr a)) (Fin (dr a)) ℂ)
    (W : Matrix (BlockIndex N dr drb) (BlockIndex N dr drb) ℂ) (a : Fin N) (i : Fin (dr a))
    (j : Fin (drb a)) (q : BlockIndex N dr drb) :
    (blockLeftOp (drb := drb) x * W) ⟨a, (i, j)⟩ q = ∑ k, x a i k * W ⟨a, (k, j)⟩ q := by
  rw [mul_apply, Fintype.sum_sigma, Finset.sum_eq_single a]
  · simp only [blockLeftOp, blockDiagonal'_apply_eq, kroneckerMap_apply, Fintype.sum_prod_type,
      one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
  · intro c _ hc
    refine Finset.sum_eq_zero fun r _ => ?_
    rw [blockLeftOp, blockDiagonal'_apply_ne _ _ _ (Ne.symm hc), zero_mul]
  · intro h; exact absurd (Finset.mem_univ a) h

lemma cbl_mul_left_apply (x : ∀ a, Matrix (Fin (dr a)) (Fin (dr a)) ℂ)
    (W : Matrix (BlockIndex N dr drb) (BlockIndex N dr drb) ℂ) (p : BlockIndex N dr drb)
    (b : Fin N) (k : Fin (dr b)) (l : Fin (drb b)) :
    (W * blockLeftOp (drb := drb) x) p ⟨b, (k, l)⟩ = ∑ i, W p ⟨b, (i, l)⟩ * x b i k := by
  rw [mul_apply, Fintype.sum_sigma, Finset.sum_eq_single b]
  · simp only [blockLeftOp, blockDiagonal'_apply_eq, kroneckerMap_apply, Fintype.sum_prod_type,
      one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · intro c _ hc
    refine Finset.sum_eq_zero fun r _ => ?_
    rw [blockLeftOp, blockDiagonal'_apply_ne _ _ _ hc, mul_zero]
  · intro h; exact absurd (Finset.mem_univ b) h

lemma cbl_commute (x : ∀ a, Matrix (Fin (dr a)) (Fin (dr a)) ℂ)
    (y : ∀ a, Matrix (Fin (drb a)) (Fin (drb a)) ℂ) :
    blockLeftOp (drb := drb) x * blockRightOp (dr := dr) y =
      blockRightOp (dr := dr) y * blockLeftOp (drb := drb) x := by
  simp only [blockLeftOp, blockRightOp, ← blockDiagonal'_mul, ← mul_kronecker_mul,
    Matrix.one_mul, Matrix.mul_one]

lemma cbl_block_comm (W : Matrix (BlockIndex N dr drb) (BlockIndex N dr drb) ℂ)
    (hW : ∀ x, blockLeftOp (drb := drb) x * W = W * blockLeftOp (drb := drb) x) :
    ∃ y, W = blockRightOp (dr := dr) y := by
  classical
  -- off-diagonal blocks vanish
  have hoff : ∀ (a b : Fin N) (i : Fin (dr a)) (j : Fin (drb a)) (k : Fin (dr b))
      (l : Fin (drb b)), a ≠ b → W ⟨a, (i, j)⟩ ⟨b, (k, l)⟩ = 0 := by
    intro a b i j k l hab
    have h := congrFun (congrFun
      (hW (Pi.single a (Matrix.single i i 1))) ⟨a, (i, j)⟩) ⟨b, (k, l)⟩
    rw [cbl_left_mul_apply, cbl_mul_left_apply] at h
    simpa [Pi.single_eq_of_ne' hab, Pi.single_eq_same, Matrix.single_apply] using h
  -- within a block
  have hdiag : ∀ (a : Fin N) (i' k k' : Fin (dr a)) (j l : Fin (drb a)),
      W ⟨a, (k, j)⟩ ⟨a, (k', l)⟩ = if k = k' then W ⟨a, (i', j)⟩ ⟨a, (i', l)⟩ else 0 := by
    intro a i' k k' j l
    have h := congrFun (congrFun
      (hW (Pi.single a (Matrix.single i' k 1))) ⟨a, (i', j)⟩) ⟨a, (k', l)⟩
    rw [cbl_left_mul_apply, cbl_mul_left_apply] at h
    simp only [Pi.single_eq_same, Matrix.single_apply] at h
    simpa only [mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul, ite_and,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, eq_comm] using h
  let y : ∀ a, Matrix (Fin (drb a)) (Fin (drb a)) ℂ := fun a =>
    if h : 0 < dr a then fun j l => W ⟨a, (⟨0, h⟩, j)⟩ ⟨a, (⟨0, h⟩, l)⟩ else 0
  refine ⟨y, ?_⟩
  ext ⟨a, i, j⟩ ⟨b, k, l⟩
  by_cases hab : a = b
  · subst hab
    have h0 : 0 < dr a := Nat.zero_lt_of_lt i.2
    rw [hdiag a ⟨0, h0⟩ i k j l]
    simp only [blockRightOp, blockDiagonal'_apply_eq, kroneckerMap_apply, one_apply, y]
    split_ifs <;> simp [h0]
  · rw [hoff a b i j k l hab, blockRightOp, blockDiagonal'_apply_ne _ _ _ hab]

theorem cbl_main {C : Type} [Fintype C] [DecidableEq C]
    (U : Matrix (BlockIndex N dr drb) C ℂ) (hU : IsUnitaryMatrix U) :
    Set.centralizer (blockAlgebraLeft U) = blockAlgebraRight U := by
  have hmid : ∀ A B : Matrix (BlockIndex N dr drb) (BlockIndex N dr drb) ℂ,
      (Uᴴ * A * U) * (Uᴴ * B * U) = Uᴴ * (A * B) * U := fun A B => by
    rw [show (Uᴴ * A * U) * (Uᴴ * B * U) = Uᴴ * A * (U * Uᴴ) * B * U by
      simp only [Matrix.mul_assoc], hU.2, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  ext Y
  simp only [Set.mem_centralizer_iff, blockAlgebraLeft, blockAlgebraRight, Set.mem_setOf_eq]
  constructor
  · intro hY
    set W := U * Y * Uᴴ with hWdef
    have hYW : Y = Uᴴ * W * U := by
      rw [hWdef, show Uᴴ * (U * Y * Uᴴ) * U = (Uᴴ * U) * Y * (Uᴴ * U) by
        simp only [Matrix.mul_assoc], hU.1, Matrix.one_mul, Matrix.mul_one]
    obtain ⟨y, hy⟩ := cbl_block_comm W fun x => by
      have h := hY _ ⟨x, rfl⟩
      rw [hYW, hmid, hmid] at h
      have := congrArg (fun Z => U * Z * Uᴴ) h
      simpa only [show ∀ Z : Matrix (BlockIndex N dr drb) (BlockIndex N dr drb) ℂ, U * (Uᴴ * Z * U) * Uᴴ = Z from fun Z => by
        rw [show U * (Uᴴ * Z * U) * Uᴴ = (U * Uᴴ) * Z * (U * Uᴴ) by
          simp only [Matrix.mul_assoc], hU.2, Matrix.one_mul, Matrix.mul_one]] using this
    exact ⟨y, hYW.trans (by rw [hy])⟩
  · rintro ⟨y, rfl⟩ X ⟨x, rfl⟩
    rw [hmid, hmid, cbl_commute]

end HarlowTASI

open HarlowTASI in
theorem solution {C : Type} [Fintype C] [DecidableEq C]
    {N : ℕ} {dr drb : Fin N → ℕ} (U : Matrix (BlockIndex N dr drb) C ℂ)
    (hU : IsUnitaryMatrix U) :
    Set.centralizer (blockAlgebraLeft U) = blockAlgebraRight U :=
  cbl_main U hU
