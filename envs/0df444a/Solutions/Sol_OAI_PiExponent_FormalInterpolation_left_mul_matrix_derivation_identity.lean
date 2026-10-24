-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.left_mul_matrix_derivation_identity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T05:27:56.17395+00:00
-- url     : https://prove2.me/submissions/932625a5-7973-49fb-96fc-fa2764845c1b

import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Trace.Defs
import Mathlib.LinearAlgebra.Basis.Defs

theorem solution
    (k L E : Type) [Field k] [Field L] [Field E]
    [Algebra k L] [Algebra k E] [Algebra L E]
    [IsScalarTower k L E] [FiniteDimensional L E]
    (d : Derivation k L L) (D : Derivation k E E)
    (hcompat : ∀ a : L, D (algebraMap L E a) = algebraMap L E (d a))
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι L E) (A : Matrix ι ι L)
    (hA : ∀ (i j : ι), A i j = b.repr (D (b j)) i) (x : E) :
    Matrix.map (Algebra.leftMulMatrix b x) d +
        A * Algebra.leftMulMatrix b x - Algebra.leftMulMatrix b x * A =
      Algebra.leftMulMatrix b (D x) := by
  -- D (a • y) = d a • y + a • D y
  have hsmul : ∀ (a : L) (y : E), D (a • y) = d a • y + a • D y := by
    intro a y
    rw [Algebra.smul_def, Derivation.leibniz, smul_eq_mul, smul_eq_mul, hcompat,
      Algebra.smul_def, Algebra.smul_def]
    ring
  have hDb : ∀ j, D (b j) = ∑ l, A l j • b l := by
    intro j
    conv_lhs => rw [← b.sum_repr (D (b j))]
    simp [hA]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply, Matrix.map_apply,
    Algebra.leftMulMatrix_eq_repr_mul]
  -- two expressions for D (x * b j)
  have e1 : D (x * b j) = x * D (b j) + b j * D x := by
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  have e2 : D (x * b j) = ∑ l, (d (b.repr (x * b j) l) • b l + b.repr (x * b j) l • D (b l)) := by
    conv_lhs => rw [← b.sum_repr (x * b j)]
    rw [map_sum]
    exact Finset.sum_congr rfl fun l _ => hsmul _ _
  have r1 : b.repr (x * D (b j)) i = ∑ l, A l j * b.repr (x * b l) i := by
    rw [hDb j, Finset.mul_sum, map_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [mul_smul_comm, map_smul, Finsupp.smul_apply, smul_eq_mul]
  have r2 : b.repr (∑ l, (d (b.repr (x * b j) l) • b l + b.repr (x * b j) l • D (b l))) i
      = d (b.repr (x * b j) i) + ∑ l, A i l * b.repr (x * b j) l := by
    rw [map_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
    simp only [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul,
      Module.Basis.repr_self, Finset.sum_add_distrib, ← hA]
    congr 1
    · simp [Finsupp.single_apply]
    · exact Finset.sum_congr rfl fun l _ => by ring
  have key := congrArg (fun y => b.repr y i) (e1.symm.trans e2)
  simp only [map_add, Finsupp.add_apply] at key
  rw [r1, r2] at key
  rw [mul_comm (D x)]
  have : ∑ l, b.repr (x * b l) i * A l j = ∑ l, A l j * b.repr (x * b l) i :=
    Finset.sum_congr rfl fun l _ => mul_comm _ _
  rw [this]
  linear_combination -key
