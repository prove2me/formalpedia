-- Prove2me | solution 1 for HarlowTASI.factorizedCode_reducedStates
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T21:08:00.970627+00:00
-- url     : https://prove2.me/submissions/df5efccd-6894-4f1b-b9ed-0c6f7f9dd610

import Mathlib
import Definitions.Def_HarlowTASI_OperatorAlgebras

open Matrix
open scoped Kronecker ComplexOrder

set_option linter.unusedSectionVars false

namespace S192FRS
open HarlowTASI

lemma VT {R Rb C : Type} [Fintype R] [DecidableEq R]
    [Fintype Rb] [DecidableEq Rb] [Fintype C] [DecidableEq C]
    (V : Matrix (R × Rb) C ℂ)
    (N : ℕ) (dr drb : Fin N → ℕ) (U : Matrix (BlockIndex N dr drb) C ℂ)
    (hU : IsUnitaryMatrix U) (ρ : Matrix C C ℂ) :
    V * ρ * Vᴴ = (V * Uᴴ) * (U * ρ * Uᴴ) * (V * Uᴴ)ᴴ := by
  have hV : V = (V * Uᴴ) * U := by rw [Matrix.mul_assoc, hU.1, Matrix.mul_one]
  conv_lhs => rw [hV]
  simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]

lemma ortho {X P : Type} [Fintype X] [DecidableEq P] (W : Matrix X P ℂ) (hW : IsIsometry W)
    (p q : P) : ∑ y, W y p * star (W y q) = if q = p then 1 else 0 := by
  have := congrFun (congrFun hW q) p
  rw [mul_apply, one_apply] at this
  rw [← this]
  exact Finset.sum_congr rfl fun y _ => by simp [mul_comm]


lemma swap4 {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (f : A → B → C → D → ℂ) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
  calc ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ a, ∑ c, ∑ b, ∑ d, f a b c d :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ a, ∑ c, ∑ d, ∑ b, f a b c d :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ d, ∑ b, f a b c d := Finset.sum_comm
    _ = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := Finset.sum_congr rfl fun c _ => Finset.sum_comm

lemma pull5 {Y A B C D : Type} [Fintype Y] [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (f : Y → A → B → C → D → ℂ) :
    ∑ y, ∑ a, ∑ b, ∑ c, ∑ d, f y a b c d = ∑ a, ∑ b, ∑ c, ∑ d, ∑ y, f y a b c d := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]

lemma rot4 {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (f : A → B → C → D → ℂ) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ c, ∑ a, ∑ d, ∑ b, f a b c d := by
  calc ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ a, ∑ c, ∑ b, ∑ d, f a b c d :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ a, ∑ c, ∑ d, ∑ b, f a b c d :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ d, ∑ b, f a b c d := Finset.sum_comm

variable {R Rb C : Type} [Fintype R] [DecidableEq R]
    [Fintype Rb] [DecidableEq Rb]
    {N : ℕ} {dr drb : Fin N → ℕ}
    {m mb : Fin N → ℕ}

-- RHS normal form
lemma rhsR (χ : ∀ a, Matrix (Fin (m a)) (Fin (mb a)) ℂ)
    (WR : Matrix R (Σ a : Fin N, Fin (dr a) × Fin (m a)) ℂ)
    (σ : Matrix (BlockIndex N dr drb) (BlockIndex N dr drb) ℂ) (x x' : R) :
    (WR * blockDiagonal' (fun a => traceRight (σ.submatrix (Sigma.mk (β := fun b => Fin (dr b) × Fin (drb b)) a)
          (Sigma.mk (β := fun b => Fin (dr b) × Fin (drb b)) a)) ⊗ₖ
        (χ a * (χ a)ᴴ)) * WRᴴ) x x' =
      ∑ a, ∑ i, ∑ k, ∑ i', ∑ k', ∑ j, ∑ l,
        WR x ⟨a, (i, k)⟩ * σ ⟨a, (i, j)⟩ ⟨a, (i', j)⟩ * (χ a k l * star (χ a k' l)) *
          star (WR x' ⟨a, (i', k')⟩) := by
  simp only [mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  rw [Fintype.sum_sigma, Finset.sum_eq_single a]
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i' _ => Finset.sum_congr rfl fun k' _ => ?_
    rw [blockDiagonal'_apply_eq, kroneckerMap_apply]
    simp only [traceRight, submatrix_apply, mul_apply, conjTranspose_apply, Finset.mul_sum,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  · intro a' _ ha'
    refine Finset.sum_eq_zero fun q _ => ?_
    simp [blockDiagonal'_apply_ne _ _ _ (Ne.symm ha')]
  · simp


lemma stepA (T : Matrix (R × Rb) (BlockIndex N dr drb) ℂ)
    (σ : Matrix (BlockIndex N dr drb) (BlockIndex N dr drb) ℂ) (x x' : R) :
    traceRight (T * σ * Tᴴ) x x' =
      ∑ b, ∑ b', σ b b' * ∑ y, T (x, y) b * star (T (x', y) b') := by
  simp only [traceRight, mul_apply, conjTranspose_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl fun b' _ => Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ =>
    Finset.sum_congr rfl fun y _ => ?_
  ring

lemma stepB (χ : ∀ a, Matrix (Fin (m a)) (Fin (mb a)) ℂ)
    (WR : Matrix R (Σ a : Fin N, Fin (dr a) × Fin (m a)) ℂ)
    (WRb : Matrix Rb (Σ a : Fin N, Fin (mb a) × Fin (drb a)) ℂ)
    (hWRb : IsIsometry WRb)
    (T : Matrix (R × Rb) (BlockIndex N dr drb) ℂ)
    (hT : ∀ x y (b : BlockIndex N dr drb), T (x, y) b =
      ∑ k, ∑ l, χ b.1 k l * WR x ⟨b.1, (b.2.1, k)⟩ * WRb y ⟨b.1, (l, b.2.2)⟩)
    (x x' : R) (b b' : BlockIndex N dr drb) :
    ∑ y, T (x, y) b * star (T (x', y) b') =
      ∑ k, ∑ l, ∑ k', ∑ l', (χ b.1 k l * WR x ⟨b.1, (b.2.1, k)⟩) *
        (star (χ b'.1 k' l') * star (WR x' ⟨b'.1, (b'.2.1, k')⟩)) *
        (if (⟨b'.1, (l', b'.2.2)⟩ : Σ a : Fin N, Fin (mb a) × Fin (drb a)) = ⟨b.1, (l, b.2.2)⟩
          then 1 else 0) := by
  simp only [← ortho WRb hWRb, hT, star_sum, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_congr rfl fun y _ => swap4 _, pull5]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ =>
    Finset.sum_congr rfl fun k' _ => Finset.sum_congr rfl fun l' _ =>
    Finset.sum_congr rfl fun y _ => ?_
  simp only [star_mul']
  ring

lemma stepC (χ : ∀ a, Matrix (Fin (m a)) (Fin (mb a)) ℂ)
    (WR : Matrix R (Σ a : Fin N, Fin (dr a) × Fin (m a)) ℂ)
    (σ : Matrix (BlockIndex N dr drb) (BlockIndex N dr drb) ℂ)
    (x x' : R) (a : Fin N) (i : Fin (dr a)) (j : Fin (drb a)) :
    ∑ b' : BlockIndex N dr drb, σ ⟨a, (i, j)⟩ b' *
      ∑ k, ∑ l, ∑ k', ∑ l', (χ a k l * WR x ⟨a, (i, k)⟩) *
        (star (χ b'.1 k' l') * star (WR x' ⟨b'.1, (b'.2.1, k')⟩)) *
        (if (⟨b'.1, (l', b'.2.2)⟩ : Σ a : Fin N, Fin (mb a) × Fin (drb a)) = ⟨a, (l, j)⟩
          then 1 else 0) =
      ∑ k, ∑ i', ∑ k', ∑ l, WR x ⟨a, (i, k)⟩ * σ ⟨a, (i, j)⟩ ⟨a, (i', j)⟩ *
        (χ a k l * star (χ a k' l)) * star (WR x' ⟨a, (i', k')⟩) := by
  rw [Fintype.sum_sigma, Finset.sum_eq_single a]
  · rw [Fintype.sum_prod_type]
    simp only [Sigma.mk.inj_iff, heq_eq_eq, Prod.mk.injEq, true_and, Finset.mul_sum]
    rw [swap4]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i' _ => ?_
    rw [Finset.sum_comm]
    simp only [ite_and, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      Finset.sum_ite_irrel, Finset.sum_const_zero]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k' _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  · intro a' _ ha'
    refine Finset.sum_eq_zero fun q _ => ?_
    simp [ha']
  · simp


lemma lhsR (χ : ∀ a, Matrix (Fin (m a)) (Fin (mb a)) ℂ)
    (WR : Matrix R (Σ a : Fin N, Fin (dr a) × Fin (m a)) ℂ)
    (WRb : Matrix Rb (Σ a : Fin N, Fin (mb a) × Fin (drb a)) ℂ)
    (hWRb : IsIsometry WRb)
    (T : Matrix (R × Rb) (BlockIndex N dr drb) ℂ)
    (hT : ∀ x y (b : BlockIndex N dr drb), T (x, y) b =
      ∑ k, ∑ l, χ b.1 k l * WR x ⟨b.1, (b.2.1, k)⟩ * WRb y ⟨b.1, (l, b.2.2)⟩)
    (σ : Matrix (BlockIndex N dr drb) (BlockIndex N dr drb) ℂ) (x x' : R) :
    traceRight (T * σ * Tᴴ) x x' =
      ∑ a, ∑ i, ∑ k, ∑ i', ∑ k', ∑ j, ∑ l,
        WR x ⟨a, (i, k)⟩ * σ ⟨a, (i, j)⟩ ⟨a, (i', j)⟩ * (χ a k l * star (χ a k' l)) *
          star (WR x' ⟨a, (i', k')⟩) := by
  rw [stepA]
  simp only [stepB χ WR WRb hWRb T hT]
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [stepC]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i' _ => ?_
  rw [Finset.sum_comm]

lemma rhsL (χ : ∀ a, Matrix (Fin (m a)) (Fin (mb a)) ℂ)
    (WRb : Matrix Rb (Σ a : Fin N, Fin (mb a) × Fin (drb a)) ℂ)
    (σ : Matrix (BlockIndex N dr drb) (BlockIndex N dr drb) ℂ) (y y' : Rb) :
    (WRb * blockDiagonal' (fun a => ((χ a)ᴴ * χ a)ᵀ ⊗ₖ
        traceLeft (σ.submatrix (Sigma.mk (β := fun b => Fin (dr b) × Fin (drb b)) a)
          (Sigma.mk (β := fun b => Fin (dr b) × Fin (drb b)) a))) * WRbᴴ) y y' =
      ∑ a, ∑ l, ∑ j, ∑ l', ∑ j', ∑ k, ∑ i,
        WRb y ⟨a, (l, j)⟩ * σ ⟨a, (i, j)⟩ ⟨a, (i, j')⟩ * (χ a k l * star (χ a k l')) *
          star (WRb y' ⟨a, (l', j')⟩) := by
  simp only [mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_sigma, Finset.sum_eq_single a]
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun l' _ => Finset.sum_congr rfl fun j' _ => ?_
    rw [blockDiagonal'_apply_eq, kroneckerMap_apply]
    simp only [traceLeft, submatrix_apply, transpose_apply, mul_apply, conjTranspose_apply,
      Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  · intro a' _ ha'
    refine Finset.sum_eq_zero fun q _ => ?_
    simp [blockDiagonal'_apply_ne _ _ _ (Ne.symm ha')]
  · simp

lemma stepAL (T : Matrix (R × Rb) (BlockIndex N dr drb) ℂ)
    (σ : Matrix (BlockIndex N dr drb) (BlockIndex N dr drb) ℂ) (y y' : Rb) :
    traceLeft (T * σ * Tᴴ) y y' =
      ∑ b, ∑ b', σ b b' * ∑ x, T (x, y) b * star (T (x, y') b') := by
  simp only [traceLeft, mul_apply, conjTranspose_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl fun b' _ => Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ =>
    Finset.sum_congr rfl fun y _ => ?_
  ring

lemma stepBL (χ : ∀ a, Matrix (Fin (m a)) (Fin (mb a)) ℂ)
    (WR : Matrix R (Σ a : Fin N, Fin (dr a) × Fin (m a)) ℂ)
    (WRb : Matrix Rb (Σ a : Fin N, Fin (mb a) × Fin (drb a)) ℂ)
    (hWR : IsIsometry WR)
    (T : Matrix (R × Rb) (BlockIndex N dr drb) ℂ)
    (hT : ∀ x y (b : BlockIndex N dr drb), T (x, y) b =
      ∑ k, ∑ l, χ b.1 k l * WR x ⟨b.1, (b.2.1, k)⟩ * WRb y ⟨b.1, (l, b.2.2)⟩)
    (y y' : Rb) (b b' : BlockIndex N dr drb) :
    ∑ x, T (x, y) b * star (T (x, y') b') =
      ∑ k, ∑ l, ∑ k', ∑ l', (χ b.1 k l * WRb y ⟨b.1, (l, b.2.2)⟩) *
        (star (χ b'.1 k' l') * star (WRb y' ⟨b'.1, (l', b'.2.2)⟩)) *
        (if (⟨b'.1, (b'.2.1, k')⟩ : Σ a : Fin N, Fin (dr a) × Fin (m a)) = ⟨b.1, (b.2.1, k)⟩
          then 1 else 0) := by
  simp only [← ortho WR hWR, hT, star_sum, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_congr rfl fun y _ => swap4 _, pull5]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ =>
    Finset.sum_congr rfl fun k' _ => Finset.sum_congr rfl fun l' _ =>
    Finset.sum_congr rfl fun y _ => ?_
  simp only [star_mul']
  ring

lemma stepCL (χ : ∀ a, Matrix (Fin (m a)) (Fin (mb a)) ℂ)
    (WRb : Matrix Rb (Σ a : Fin N, Fin (mb a) × Fin (drb a)) ℂ)
    (σ : Matrix (BlockIndex N dr drb) (BlockIndex N dr drb) ℂ)
    (y y' : Rb) (a : Fin N) (i : Fin (dr a)) (j : Fin (drb a)) :
    ∑ b' : BlockIndex N dr drb, σ ⟨a, (i, j)⟩ b' *
      ∑ k, ∑ l, ∑ k', ∑ l', (χ a k l * WRb y ⟨a, (l, j)⟩) *
        (star (χ b'.1 k' l') * star (WRb y' ⟨b'.1, (l', b'.2.2)⟩)) *
        (if (⟨b'.1, (b'.2.1, k')⟩ : Σ a : Fin N, Fin (dr a) × Fin (m a)) = ⟨a, (i, k)⟩
          then 1 else 0) =
      ∑ l, ∑ j', ∑ l', ∑ k, WRb y ⟨a, (l, j)⟩ * σ ⟨a, (i, j)⟩ ⟨a, (i, j')⟩ *
        (χ a k l * star (χ a k l')) * star (WRb y' ⟨a, (l', j')⟩) := by
  rw [Fintype.sum_sigma, Finset.sum_eq_single a]
  · rw [Fintype.sum_prod_type]
    simp only [Sigma.mk.inj_iff, heq_eq_eq, Prod.mk.injEq, true_and, Finset.mul_sum]
    simp only [ite_and, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      Finset.sum_ite_irrel, Finset.sum_const_zero]
    refine (rot4 _).trans ?_
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j' _ =>
      Finset.sum_congr rfl fun l' _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  · intro a' _ ha'
    refine Finset.sum_eq_zero fun q _ => ?_
    simp [ha']
  · simp

lemma lhsL (χ : ∀ a, Matrix (Fin (m a)) (Fin (mb a)) ℂ)
    (WR : Matrix R (Σ a : Fin N, Fin (dr a) × Fin (m a)) ℂ)
    (WRb : Matrix Rb (Σ a : Fin N, Fin (mb a) × Fin (drb a)) ℂ)
    (hWR : IsIsometry WR)
    (T : Matrix (R × Rb) (BlockIndex N dr drb) ℂ)
    (hT : ∀ x y (b : BlockIndex N dr drb), T (x, y) b =
      ∑ k, ∑ l, χ b.1 k l * WR x ⟨b.1, (b.2.1, k)⟩ * WRb y ⟨b.1, (l, b.2.2)⟩)
    (σ : Matrix (BlockIndex N dr drb) (BlockIndex N dr drb) ℂ) (y y' : Rb) :
    traceLeft (T * σ * Tᴴ) y y' =
      ∑ a, ∑ l, ∑ j, ∑ l', ∑ j', ∑ k, ∑ i,
        WRb y ⟨a, (l, j)⟩ * σ ⟨a, (i, j)⟩ ⟨a, (i, j')⟩ * (χ a k l * star (χ a k l')) *
          star (WRb y' ⟨a, (l', j')⟩) := by
  rw [stepAL]
  simp only [stepBL χ WR WRb hWR T hT]
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fintype.sum_prod_type]
  simp only [stepCL]
  refine (pull5 _).trans ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l' _ => Finset.sum_congr rfl fun j' _ => ?_
  rw [Finset.sum_comm]

end S192FRS

open HarlowTASI in
theorem solution {R Rb C : Type} [Fintype R] [DecidableEq R]
    [Fintype Rb] [DecidableEq Rb] [Fintype C] [DecidableEq C]
    (V : Matrix (R × Rb) C ℂ)
    (N : ℕ) (dr drb : Fin N → ℕ) (U : Matrix (BlockIndex N dr drb) C ℂ)
    (hU : IsUnitaryMatrix U)
    (m mb : Fin N → ℕ) (χ : ∀ a, Matrix (Fin (m a)) (Fin (mb a)) ℂ)
    (WR : Matrix R (Σ a : Fin N, Fin (dr a) × Fin (m a)) ℂ)
    (WRb : Matrix Rb (Σ a : Fin N, Fin (mb a) × Fin (drb a)) ℂ)
    (hWR : IsIsometry WR) (hWRb : IsIsometry WRb)
    (hVU : ∀ (x : R) (y : Rb) (a : Fin N) (i : Fin (dr a)) (j : Fin (drb a)),
        (V * Uᴴ) (x, y) ⟨a, (i, j)⟩ =
          ∑ k, ∑ l, χ a k l * WR x ⟨a, (i, k)⟩ * WRb y ⟨a, (l, j)⟩)
    (ρ : Matrix C C ℂ) :
    traceRight (V * ρ * Vᴴ) =
        WR * blockDiagonal' (fun a => traceRight (diagBlock U ρ a) ⊗ₖ (χ a * (χ a)ᴴ)) * WRᴴ ∧
    traceLeft (V * ρ * Vᴴ) =
        WRb * blockDiagonal' (fun a => ((χ a)ᴴ * χ a)ᵀ ⊗ₖ traceLeft (diagBlock U ρ a)) * WRbᴴ := by
  have hT : ∀ x y (b : BlockIndex N dr drb), (V * Uᴴ) (x, y) b =
      ∑ k, ∑ l, χ b.1 k l * WR x ⟨b.1, (b.2.1, k)⟩ * WRb y ⟨b.1, (l, b.2.2)⟩ := by
    rintro x y ⟨a, i, j⟩; exact hVU x y a i j
  rw [S192FRS.VT V N dr drb U hU ρ]
  constructor
  · ext x x'
    rw [S192FRS.lhsR χ WR WRb hWRb _ hT]
    exact (S192FRS.rhsR χ WR (U * ρ * Uᴴ) x x').symm
  · ext y y'
    rw [S192FRS.lhsL χ WR WRb hWR _ hT]
    exact (S192FRS.rhsL χ WRb (U * ρ * Uᴴ) y y').symm

