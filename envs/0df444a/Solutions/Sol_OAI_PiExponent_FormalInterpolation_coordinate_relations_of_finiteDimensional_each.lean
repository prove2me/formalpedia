-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.coordinate_relations_of_finiteDimensional_each
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T15:54:42.019209+00:00
-- url     : https://prove2.me/submissions/e9b7b644-a053-48fa-916c-ddc0334c965c

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
    ∀ i : Fin (m + 1), ∃ n : Nat, 0 < n ∧ ∃ c : Fin n → Complex,
      MvPolynomial.X i ^ n -
        ∑ k : Fin n, MvPolynomial.C (c k) * MvPolynomial.X i ^ k.val ∈ J := by
  haveI := hfd
  by_cases hJ : J = ⊤
  · intro i
    exact ⟨1, one_pos, fun _ => 0, by rw [hJ]; exact Submodule.mem_top⟩
  haveI : Nontrivial ((MvPolynomial (Fin (m + 1)) Complex) ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ
  intro i
  set x := Ideal.Quotient.mk J (MvPolynomial.X i)
  have hint : IsIntegral Complex x := Algebra.IsIntegral.isIntegral x
  refine ⟨(minpoly Complex x).natDegree, minpoly.natDegree_pos hint, fun k => -(minpoly Complex x).coeff k, ?_⟩
  exact pie_rel_of_monic J i _ (minpoly.monic hint) (minpoly.aeval Complex x)
