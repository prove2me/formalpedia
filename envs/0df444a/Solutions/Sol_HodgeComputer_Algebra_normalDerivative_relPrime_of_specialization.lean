-- Prove2me | solution 1 for HodgeComputer.Algebra.normalDerivative_relPrime_of_specialization
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T03:37:50.528794+00:00
-- url     : https://prove2.me/submissions/5a423822-66f4-4d1c-955d-8e8a1ccb9ac9

import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.MvPolynomial.Homogeneous

set_option autoImplicit false

private theorem relPrime_of_specialization {R K : Type*} [CommRing R] [IsDomain R]
    [CommRing K] [IsDomain K] (φ : R →+* K) (f g : Polynomial R)
    (hf : IsUnit f.leadingCoeff)
    (hfg : IsRelPrime (f.map φ) (g.map φ)) : IsRelPrime f g := by
  intro d hdf hdg
  apply Polynomial.isUnit_of_isUnit_leadingCoeff_of_isUnit_map φ
  · exact isUnit_of_dvd_unit (Polynomial.leadingCoeff_dvd_leadingCoeff hdf) hf
  · exact hfg (map_dvd (Polynomial.mapRingHom φ) hdf)
      (map_dvd (Polynomial.mapRingHom φ) hdg)

private theorem split_deriv {R : Type*} [CommRing R] (n : ℕ)
    (p : MvPolynomial (Fin (n + 1)) R) :
    MvPolynomial.finSuccEquiv R n (MvPolynomial.pderiv 0 p) =
      Polynomial.derivative (MvPolynomial.finSuccEquiv R n p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [MvPolynomial.finSuccEquiv_apply, MvPolynomial.pderiv_C]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    induction i using Fin.cases with
    | zero =>
      simp [MvPolynomial.finSuccEquiv_X_zero, Polynomial.derivative_mul, hp,
        mul_comm, add_comm]
    | succ i =>
      simp [MvPolynomial.finSuccEquiv_X_succ, Polynomial.derivative_mul,
        ← hp, Fin.succ_ne_zero, mul_comm]

theorem solution {K : Type*} [Field K] (n d : ℕ)
    (f : MvPolynomial (Fin (n + 1)) K) (a : K) (v : Fin n → K)
    (hf : f.IsHomogeneous d) (ha : a ≠ 0)
    (hc : (MvPolynomial.finSuccEquiv K n f).coeff d = MvPolynomial.C a)
    (hs : IsRelPrime ((MvPolynomial.finSuccEquiv K n f).map (MvPolynomial.eval v))
      (Polynomial.derivative ((MvPolynomial.finSuccEquiv K n f).map (MvPolynomial.eval v)))) :
    IsRelPrime f (MvPolynomial.pderiv 0 f) := by
  have hdeg : (MvPolynomial.finSuccEquiv K n f).natDegree ≤ d :=
    (MvPolynomial.natDegree_finSuccEquiv f).le.trans
      ((MvPolynomial.degreeOf_le_totalDegree f 0).trans hf.totalDegree_le)
  have hc0 : (MvPolynomial.finSuccEquiv K n f).coeff d ≠ 0 := by
    rw [hc]
    exact MvPolynomial.C_ne_zero.mpr ha
  have hlc : IsUnit (MvPolynomial.finSuccEquiv K n f).leadingCoeff := by
    rw [Polynomial.leadingCoeff, Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hdeg hc0, hc]
    exact (isUnit_iff_ne_zero.mpr ha).map MvPolynomial.C
  apply IsRelPrime.of_map (MvPolynomial.finSuccEquiv K n).toRingEquiv
  apply relPrime_of_specialization (MvPolynomial.eval v) _ _ hlc
  change IsRelPrime ((MvPolynomial.finSuccEquiv K n f).map (MvPolynomial.eval v))
    ((MvPolynomial.finSuccEquiv K n (MvPolynomial.pderiv 0 f)).map (MvPolynomial.eval v))
  simpa only [split_deriv, ← Polynomial.derivative_map] using hs

#print axioms solution
