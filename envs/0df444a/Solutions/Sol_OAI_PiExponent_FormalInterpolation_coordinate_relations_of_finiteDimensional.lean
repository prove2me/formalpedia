-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.coordinate_relations_of_finiteDimensional
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T15:54:51.239989+00:00
-- url     : https://prove2.me/submissions/4a23aa9e-c206-4612-92fa-13c7d8e4f06f

import Mathlib
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

open scoped BigOperators
theorem pie_rel_of_monic {m : Nat}
    (J : Ideal (MvPolynomial (Fin (m + 1)) Complex)) (i : Fin (m + 1)) (q : Polynomial Complex)
    (hq : q.Monic)
    (hx : Polynomial.aeval (Ideal.Quotient.mk J (MvPolynomial.X i)) q = 0) :
    MvPolynomial.X i ^ q.natDegree -
      ∑ k : Fin q.natDegree, MvPolynomial.C (-q.coeff k) * MvPolynomial.X i ^ k.val ∈ J := by
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  rw [hq.as_sum] at hx
  rw [← hx]
  simp only [map_sub, map_sum, map_mul, map_pow, map_add, Polynomial.aeval_X_pow, Polynomial.aeval_C,
    Polynomial.aeval_X]
  rw [Fin.sum_univ_eq_sum_range (fun k => (Ideal.Quotient.mk J) (MvPolynomial.C (-q.coeff k)) *
    (Ideal.Quotient.mk J) (MvPolynomial.X i) ^ k) q.natDegree]
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl; intro k _
  have hc : (algebraMap Complex ((MvPolynomial (Fin (m + 1)) Complex) ⧸ J)) (q.coeff k) =
      Ideal.Quotient.mk J (MvPolynomial.C (q.coeff k)) := rfl
  rw [hc, MvPolynomial.C_neg, map_neg]
  ring

theorem solution
    {m : Nat}
    (J : Ideal (MvPolynomial (Fin (m + 1)) Complex))
    (hfd : FiniteDimensional Complex ((MvPolynomial (Fin (m + 1)) Complex) ⧸ J)) :
    ∃ N : Nat, 0 < N ∧
      ∀ i : Fin (m + 1), ∃ c : Fin N → Complex,
        MvPolynomial.X i ^ N -
          ∑ k : Fin N, MvPolynomial.C (c k) * MvPolynomial.X i ^ k.val ∈ J := by
  haveI := hfd
  by_cases hJ : J = ⊤
  · exact ⟨1, one_pos, fun i => ⟨fun _ => 0, by rw [hJ]; exact Submodule.mem_top⟩⟩
  haveI : Nontrivial ((MvPolynomial (Fin (m + 1)) Complex) ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ
  have hint : ∀ i : Fin (m + 1), IsIntegral Complex (Ideal.Quotient.mk J (MvPolynomial.X i)) :=
    fun i => Algebra.IsIntegral.isIntegral _
  set d : Fin (m + 1) → ℕ := fun i => (minpoly Complex (Ideal.Quotient.mk J (MvPolynomial.X i))).natDegree
  set N := ∑ i, d i
  have hdN : ∀ i, d i ≤ N := fun i => Finset.single_le_sum (fun j _ => Nat.zero_le (d j)) (Finset.mem_univ i)
  have hdpos : ∀ i, 0 < d i := fun i => minpoly.natDegree_pos (hint i)
  refine ⟨N, lt_of_lt_of_le (hdpos 0) (hdN 0), fun i => ?_⟩
  set p := minpoly Complex (Ideal.Quotient.mk J (MvPolynomial.X i))
  set q := p * Polynomial.X ^ (N - d i)
  have hq : q.Monic := (minpoly.monic (hint i)).mul (Polynomial.monic_X_pow _)
  have hqdeg : q.natDegree = N := by
    rw [(minpoly.monic (hint i)).natDegree_mul (Polynomial.monic_X_pow _), Polynomial.natDegree_X_pow]
    have := hdN i
    simp only [d] at this ⊢
    omega
  have hx : Polynomial.aeval (Ideal.Quotient.mk J (MvPolynomial.X i)) q = 0 := by
    rw [map_mul, minpoly.aeval, zero_mul]
  have h := pie_rel_of_monic J i q hq hx
  rw [hqdeg] at h
  exact ⟨fun k => -q.coeff k, h⟩
