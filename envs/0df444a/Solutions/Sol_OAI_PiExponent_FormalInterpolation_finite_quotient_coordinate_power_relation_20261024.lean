-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.finite_quotient_coordinate_power_relation_20261024
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-24T15:36:12.763799+00:00
-- url     : https://prove2.me/submissions/2186b8ac-5b2e-43df-be12-2db83c12bfc4

import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
open scoped BigOperators

theorem solution
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (hfinite : Module.Finite Complex (MvPolynomial (Fin d) Complex ⧸ I))
    (i : Fin d) :
    ∃ (N : Nat) (c : Fin (N + 1) → Complex),
      (∃ k, c k ≠ 0) ∧
      (∑ k : Fin (N + 1),
        MvPolynomial.C (c k) * MvPolynomial.X i ^ (k : Nat)) ∈ I := by
  classical
  letI : Module.Finite Complex (MvPolynomial (Fin d) Complex ⧸ I) := hfinite
  let Q := MvPolynomial (Fin d) Complex ⧸ I
  let N : Nat := Module.finrank Complex Q
  let v : Fin (N + 1) → Q := fun k =>
    (Ideal.Quotient.mk I (MvPolynomial.X i)) ^ (k : Nat)
  have hnot : ¬ LinearIndependent Complex v := by
    intro hli
    have hcard := hli.fintype_card_le_finrank
    exact (Nat.not_succ_le_self N)
      (by simpa [N, Fintype.card_fin] using hcard)
  obtain ⟨c, hsum, k, hk⟩ := Fintype.not_linearIndependent_iff.mp hnot
  refine ⟨N, c, ⟨k, hk⟩, ?_⟩
  have hterm (x : Fin (N + 1)) :
      Ideal.Quotient.mk I
          (MvPolynomial.C (c x) * MvPolynomial.X i ^ (x : Nat)) =
        c x • (Ideal.Quotient.mk I (MvPolynomial.X i)) ^ (x : Nat) := by
    rw [map_mul, map_pow, ← MvPolynomial.algebraMap_eq,
      Ideal.Quotient.mk_algebraMap, ← Algebra.smul_def]
  have hmap : Ideal.Quotient.mk I
      (∑ x : Fin (N + 1),
        MvPolynomial.C (c x) * MvPolynomial.X i ^ (x : Nat)) = 0 := by
    rw [map_sum]
    simp_rw [hterm]
    exact hsum
  exact (Ideal.Quotient.eq_zero_iff_mem).mp hmap