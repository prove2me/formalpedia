-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.mvPolynomial_diagonal_binomial_coeff
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-20T13:19:53.385542+00:00
-- url     : https://prove2.me/submissions/4f0098c6-320b-422c-a477-4090b168b37c

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_TranslatedExpansion_CollisionAnalyticHelpers
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_TranslatedExpansionTerms
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.Coeff

open scoped BigOperators Topology
open OAI.PiExponent.LiteralAnalytic.TranslatedExpansion
open OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.CollisionAnalytic

private theorem separated_binomial_coeff
    {R : Type*} [CommSemiring R] {m : ℕ}
    (c : Fin m → R) (a : Fin m → ℕ) (A : Fin m →₀ ℕ) :
    (∏ i : Fin m, (MvPolynomial.C (c i) + MvPolynomial.X i) ^ a i).coeff A =
      ∏ i : Fin m, ((a i).choose (A i) : R) * c i ^ (a i - A i) := by
  classical
  induction m with
  | zero =>
      have hA : A = 0 := by
        ext i
        exact Fin.elim0 i
      simp [hA]
  | succ m ih =>
      let P : MvPolynomial (Fin m) R :=
        ∏ i : Fin m,
          (MvPolynomial.C (c i.succ) + MvPolynomial.X i) ^ a i.succ
      let q : Polynomial (MvPolynomial (Fin m) R) :=
        (Polynomial.X + Polynomial.C (MvPolynomial.C (c 0))) ^ a 0
      have hC (r : R) :
          MvPolynomial.finSuccEquiv R m (MvPolynomial.C r) =
            Polynomial.C (MvPolynomial.C r) := by
        simp only [MvPolynomial.finSuccEquiv_apply, MvPolynomial.eval₂Hom_C,
          RingHom.comp_apply]
      have hE :
          MvPolynomial.finSuccEquiv R m
            (∏ i : Fin (m + 1),
              (MvPolynomial.C (c i) + MvPolynomial.X i) ^ a i) =
            q * Polynomial.C P := by
        dsimp only [q, P]
        simp only [Fin.prod_univ_succ, map_mul, map_pow, map_add, map_prod,
          hC, MvPolynomial.finSuccEquiv_X_zero, MvPolynomial.finSuccEquiv_X_succ,
          Polynomial.C_pow, Polynomial.C_add]
        rw [add_comm (Polynomial.C (MvPolynomial.C (c 0))) Polynomial.X]
      have hq :
          q.coeff (A 0) =
            MvPolynomial.C (((a 0).choose (A 0) : R) * c 0 ^ (a 0 - A 0)) := by
        dsimp only [q]
        rw [Polynomial.coeff_X_add_C_pow]
        simp only [map_mul, map_pow, map_natCast]
        exact mul_comm _ _
      calc
        (∏ i : Fin (m + 1),
            (MvPolynomial.C (c i) + MvPolynomial.X i) ^ a i).coeff A =
            MvPolynomial.coeff A.tail
              ((MvPolynomial.finSuccEquiv R m
                (∏ i : Fin (m + 1),
                  (MvPolynomial.C (c i) + MvPolynomial.X i) ^ a i)).coeff (A 0)) := by
          simpa only [Finsupp.cons_tail] using
            (MvPolynomial.finSuccEquiv_coeff_coeff A.tail
              (∏ i : Fin (m + 1),
                (MvPolynomial.C (c i) + MvPolynomial.X i) ^ a i) (A 0)).symm
        _ = ∏ i : Fin (m + 1),
              ((a i).choose (A i) : R) * c i ^ (a i - A i) := by
          rw [hE, Polynomial.coeff_mul_C, hq, MvPolynomial.coeff_C_mul]
          dsimp only [P]
          rw [ih (fun i => c i.succ) (fun i => a i.succ) A.tail]
          simp only [Fin.prod_univ_succ, Finsupp.tail_apply]

theorem solution
    {m : ℕ} (u s : PowerSeries ℂ) (a : Fin m → ℕ)
    (A : Fin m →₀ ℕ) :
    (MvPolynomial.C u *
      ∏ i : Fin m, (MvPolynomial.C s + MvPolynomial.X i) ^ a i).coeff A =
      u * PowerSeries.C ((∏ i, (a i).choose (A i) : ℕ) : ℂ) *
        s ^ (∑ i : Fin m, (a i - A i)) := by
  rw [MvPolynomial.coeff_C_mul,
    separated_binomial_coeff (fun _ : Fin m => s) a A]
  simp only [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    map_prod, map_natCast, Nat.cast_prod, mul_assoc]