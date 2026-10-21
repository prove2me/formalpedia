-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.flattened_coeff_finsupp_monomial
-- status  : ACCEPTED   (prove)
-- author  : @polylog
-- created : 2026-10-20T16:11:29.048986+00:00
-- url     : https://prove2.me/submissions/9802e0a0-2441-4300-9e9b-27e83e7dc74e

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.Algebra.MvPolynomial.Equiv

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem solution
    {m : Nat} (p : Polynomial Complex) (d : Fin m →₀ Nat)
    (e : Fin (m + 1) →₀ Nat) :
    (MvPolynomial.eval₂Hom
      (((Polynomial.aeval (MvPolynomial.X (0 : Fin (m + 1)))) :
        Polynomial Complex →ₐ[Complex] MvPolynomial (Fin (m + 1)) Complex).toRingHom)
      (fun i : Fin m => MvPolynomial.X i.succ)
      (MvPolynomial.monomial d p)).coeff e =
      ((MvPolynomial.monomial d p).coeff
        (InterpolationMatrix.exponentVector (fun i => e i.succ))).coeff (e 0) := by
  classical
  set v : Fin m →₀ Nat := InterpolationMatrix.exponentVector (fun i => e i.succ) with hv
  set A : MvPolynomial (Fin (m + 1)) Complex :=
    MvPolynomial.eval₂Hom
      (((Polynomial.aeval (MvPolynomial.X (0 : Fin (m + 1)))) :
        Polynomial Complex →ₐ[Complex] MvPolynomial (Fin (m + 1)) Complex).toRingHom)
      (fun i : Fin m => MvPolynomial.X i.succ)
      (MvPolynomial.monomial d p) with hAdef
  have he : Finsupp.cons (e 0) v = e := by
    ext j
    refine Fin.cases ?_ (fun k => ?_) j
    · simp [v, InterpolationMatrix.exponentVector]
    · simp [v, InterpolationMatrix.exponentVector]
  have hA : (MvPolynomial.finSuccEquiv Complex m) ((Polynomial.aeval (MvPolynomial.X (0 : Fin (m + 1)))) p)
      = Polynomial.map (MvPolynomial.C : Complex →+* MvPolynomial (Fin m) Complex) p := by
    rw [← Polynomial.aeval_algHom_apply (MvPolynomial.finSuccEquiv Complex m)]
    rw [MvPolynomial.finSuccEquiv_X_zero]
    simpa only [MvPolynomial.algebraMap_eq] using
      (Polynomial.aeval_X_left_eq_map (S := MvPolynomial (Fin m) Complex) p)
  have hF : (MvPolynomial.finSuccEquiv Complex m) A =
      Polynomial.map (MvPolynomial.C : Complex →+* MvPolynomial (Fin m) Complex) p *
        Polynomial.C ((MvPolynomial.monomial d) (1 : Complex)) := by
    rw [hAdef]
    rw [MvPolynomial.eval₂Hom_monomial]
    change (MvPolynomial.finSuccEquiv Complex m)
        ((Polynomial.aeval (MvPolynomial.X (0 : Fin (m + 1)))) p *
          (d.prod fun i k => MvPolynomial.X i.succ ^ k)) =
      Polynomial.map (MvPolynomial.C : Complex →+* MvPolynomial (Fin m) Complex) p *
        Polynomial.C ((MvPolynomial.monomial d) (1 : Complex))
    have hprod : (MvPolynomial.finSuccEquiv Complex m)
        (d.prod fun i k => MvPolynomial.X i.succ ^ k) =
        Polynomial.C ((MvPolynomial.monomial d) (1 : Complex)) := by
      rw [MvPolynomial.monomial_eq, map_one, one_mul]
      simp only [Finsupp.prod, map_prod, map_pow, MvPolynomial.finSuccEquiv_X_succ]
    rw [map_mul, hA, hprod]
  change A.coeff e = ((MvPolynomial.monomial d p).coeff v).coeff (e 0)
  calc
    A.coeff e = MvPolynomial.coeff v ((MvPolynomial.finSuccEquiv Complex m A).coeff (e 0)) := by
      rw [MvPolynomial.finSuccEquiv_coeff_coeff, he]
    _ = ((MvPolynomial.monomial d p).coeff v).coeff (e 0) := by
      rw [hF, Polynomial.coeff_mul_C, Polynomial.coeff_map,
        MvPolynomial.C_mul_monomial, mul_one]
      by_cases hd : d = v <;> simp [MvPolynomial.coeff_monomial, hd]
