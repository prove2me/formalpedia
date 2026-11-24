-- Prove2me | solution 1 for HodgeComputer.Formal.HoldoutCover.irreducible_power_add_constant
-- status  : ACCEPTED   (prove)
-- author  : @benediamond
-- created : 2026-11-24T03:18:10.943397+00:00
-- url     : https://prove2.me/submissions/d10652dc-18e1-4f3b-8792-164b56256804

import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Tactic

set_option autoImplicit false

namespace HodgeComputerFormalIrredAux
/- Source component: HypersurfaceDomain -/
section
/-!
Domain lemmas for the Fermat-curve base and its weighted quotient hypersurface.
These are intermediate construction lemmas, not a HasCertificate theorem.
Prepared with OpenAI ChatGPT assistance for contribution through fqlx.
-/

noncomputable section

namespace HoldoutConstruction

open Polynomial

section MonicEmbedding

variable {R T : Type*} [CommRing R] [CommRing T]

/-- A monic polynomial quotient embeds after any injective coefficient map. -/
theorem adjoinRoot_map_injective (φ : R →+* T) (hφ : Function.Injective φ)
    (f : R[X]) (hf : f.Monic) :
    Function.Injective (AdjoinRoot.map φ f (f.map φ) (dvd_refl _)) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  induction z using AdjoinRoot.induction_on with
  | ih p =>
    have hp : (f.map φ) ∣ p.map φ := by
      change p.eval₂ ((AdjoinRoot.of (f.map φ)).comp φ)
        (AdjoinRoot.root (f.map φ)) = 0 at hz
      rw [← Polynomial.eval₂_map, ← AdjoinRoot.algebraMap_eq,
        ← Polynomial.aeval_def, AdjoinRoot.aeval_eq] at hz
      exact AdjoinRoot.mk_eq_zero.mp hz
    exact AdjoinRoot.mk_eq_zero.mpr ((Polynomial.map_dvd_map φ hφ hf).mp hp)

/-- Domainhood of a monic polynomial quotient descends along an injective
coefficient map. -/
theorem adjoinRoot_isDomain_of_monic_map (φ : R →+* T) (hφ : Function.Injective φ)
    (f : R[X]) (hf : f.Monic) [IsDomain (AdjoinRoot (f.map φ))] :
    IsDomain (AdjoinRoot f) :=
  (adjoinRoot_map_injective φ hφ f hf).isDomain _

end MonicEmbedding

section Eisenstein

variable {R : Type*} [CommRing R] [IsDomain R]

/-- A simple zero of the constant coefficient gives an elementary Eisenstein
criterion for the outer polynomial. The two occurrences of `X` belong to
different polynomial rings. -/
theorem irreducible_power_add_constant (g : R[X])
    (h0 : g.coeff 0 = 0) (h1 : g.coeff 1 ≠ 0) (n : ℕ) (hn : 0 < n) :
    Irreducible ((X : (R[X])[X])^n + C g) := by
  let P : Ideal R[X] := Ideal.span {X}
  have hP : P.IsPrime := (Ideal.span_singleton_prime (by simp)).mpr Polynomial.prime_X
  have hm : ((X : (R[X])[X])^n + C g).Monic :=
    monic_X_pow_add_C g (Nat.ne_of_gt hn)
  have he : ((X : (R[X])[X])^n + C g).IsEisensteinAt P :=
    hm.isEisensteinAt_of_mem_of_notMem hP.ne_top (by
      intro k hk
      rw [natDegree_X_pow_add_C] at hk
      simp only [coeff_add, coeff_X_pow, if_neg (Nat.ne_of_lt hk), zero_add, coeff_C]
      split_ifs
      · exact Ideal.mem_span_singleton.mpr (Polynomial.X_dvd_iff.mpr h0)
      · exact Ideal.zero_mem P) (by
      simp only [coeff_add, coeff_X_pow, if_neg (Nat.ne_of_lt hn), coeff_C_zero,
        zero_add]
      intro hg
      have hd : (X : R[X])^2 ∣ g := by
        simpa only [P, Ideal.span_singleton_pow, Ideal.mem_span_singleton] using hg
      exact h1 ((Polynomial.X_pow_dvd_iff.mp hd) 1 (by decide)))
  exact he.irreducible hP hm.isPrimitive (by simpa using hn)

end Eisenstein

section QuotientHypersurface

variable {R : Type*} [CommRing R]

/-- The weighted quotient equation, viewed as a monic polynomial in `X0`.
The four coefficient variables are `X1`, `X2`, `S`, and `P`, in this order. -/
def quotientPolynomial (alpha beta : R) : (MvPolynomial (Fin 4) R)[X] :=
  X^6 + (C (MvPolynomial.C alpha * MvPolynomial.X 0 * MvPolynomial.X 3) * X^3 +
    C (MvPolynomial.X 0^6 + MvPolynomial.X 1^6 +
      MvPolynomial.C beta * MvPolynomial.X 0^3 * MvPolynomial.X 1 * MvPolynomial.X 3 +
      MvPolynomial.X 2^3 - 3 * MvPolynomial.X 2 * MvPolynomial.X 3^2))

theorem quotientPolynomial_monic (alpha beta : R) :
    (quotientPolynomial alpha beta).Monic := by
  apply monic_X_pow_add
  apply lt_of_le_of_lt (degree_add_le _ _)
  apply max_lt
  · exact lt_of_le_of_lt (degree_C_mul_X_pow_le 3 _) (by decide)
  · exact lt_of_le_of_lt degree_C_le (by decide)

/-- This specialization fixes `S`, sets `X1=X2=0`, and sets `P=1`. -/
def quotientSpecialization : MvPolynomial (Fin 4) R →+* R[X] :=
  MvPolynomial.eval₂Hom C ![0, 0, X, 1]

theorem quotientPolynomial_specialization (alpha beta : R) :
    (quotientPolynomial alpha beta).map quotientSpecialization =
      (X : (R[X])[X])^6 + C (X^3 - 3*X) := by
  simp [quotientPolynomial, quotientSpecialization]

theorem quotientPolynomial_irreducible [IsDomain R] [CharZero R]
    (alpha beta : R) : Irreducible (quotientPolynomial alpha beta) := by
  apply (quotientPolynomial_monic alpha beta).irreducible_of_irreducible_map
    quotientSpecialization
  rw [quotientPolynomial_specialization]
  exact irreducible_power_add_constant (X^3 - 3*X : R[X])
    (by simp) (by norm_num) 6 (by decide)

theorem quotientPolynomial_map {T : Type*} [CommRing T]
    (φ : R →+* T) (alpha beta : R) :
    (quotientPolynomial alpha beta).map (MvPolynomial.map φ) =
      quotientPolynomial (φ alpha) (φ beta) := by
  simp [quotientPolynomial]

/-- The affine weighted quotient is integral over every characteristic-zero
coefficient domain, including the coordinate domain of the Fermat base curve.
Unique factorization is used only after passing to the coefficient fraction
field; monicity descends domainhood back to the original coefficient ring. -/
theorem quotient_adjoinRoot_isDomain [IsDomain R] [CharZero R]
    (alpha beta : R) : IsDomain (AdjoinRoot (quotientPolynomial alpha beta)) := by
  let φ : R →+* FractionRing R := algebraMap R (FractionRing R)
  have hφ : Function.Injective φ := IsFractionRing.injective R (FractionRing R)
  have hmap : IsDomain (AdjoinRoot
      ((quotientPolynomial alpha beta).map (MvPolynomial.map φ))) := by
    rw [quotientPolynomial_map]
    exact AdjoinRoot.isDomain_of_prime
      (quotientPolynomial_irreducible (φ alpha) (φ beta)).prime
  let := hmap
  exact adjoinRoot_isDomain_of_monic_map (MvPolynomial.map φ)
    (MvPolynomial.map_injective φ hφ) _ (quotientPolynomial_monic alpha beta)

end QuotientHypersurface

section FermatBase

variable {R : Type*} [CommRing R]

/-- The affine Fermat-curve equation `alpha^6 + beta^6 = 1`, viewed as a
monic polynomial in `alpha` with coefficients in `R[beta]`. -/
def fermatCurvePolynomial : (R[X])[X] := X^6 + C (X^6 - 1)

theorem fermatCurvePolynomial_monic : (fermatCurvePolynomial (R := R)).Monic :=
  monic_X_pow_add_C _ (by decide)

theorem fermatCurvePolynomial_irreducible [IsDomain R] [CharZero R] :
    Irreducible (fermatCurvePolynomial (R := R)) := by
  apply (fermatCurvePolynomial_monic (R := R)).irreducible_of_irreducible_map
    (Polynomial.eval₂RingHom C (X+1))
  have he : (fermatCurvePolynomial (R := R)).map
      (Polynomial.eval₂RingHom C (X+1)) = X^6 + C ((X+1)^6 - 1) := by
    simp [fermatCurvePolynomial]
  rw [he]
  exact irreducible_power_add_constant ((X+1)^6 - 1 : R[X])
    (by simp [coeff_X_add_one_pow]) (by norm_num [coeff_X_add_one_pow, coeff_one])
    6 (by decide)

theorem fermatCurvePolynomial_map {T : Type*} [CommRing T] (φ : R →+* T) :
    (fermatCurvePolynomial (R := R)).map (Polynomial.mapRingHom φ) =
      fermatCurvePolynomial (R := T) := by
  simp [fermatCurvePolynomial]

/-- The affine Fermat-curve coordinate ring is a domain over every
characteristic-zero coefficient domain. -/
theorem fermatCurve_adjoinRoot_isDomain [IsDomain R] [CharZero R] :
    IsDomain (AdjoinRoot (fermatCurvePolynomial (R := R))) := by
  let φ : R →+* FractionRing R := algebraMap R (FractionRing R)
  have hφ : Function.Injective φ := IsFractionRing.injective R (FractionRing R)
  have hmap : IsDomain (AdjoinRoot
      ((fermatCurvePolynomial (R := R)).map (Polynomial.mapRingHom φ))) := by
    rw [fermatCurvePolynomial_map]
    exact AdjoinRoot.isDomain_of_prime
      (fermatCurvePolynomial_irreducible (R := FractionRing R)).prime
  let := hmap
  exact adjoinRoot_isDomain_of_monic_map (Polynomial.mapRingHom φ)
    (Polynomial.map_injective φ hφ) _ fermatCurvePolynomial_monic

end FermatBase

end HoldoutConstruction

end
end

end HodgeComputerFormalIrredAux

open scoped Polynomial in
theorem solution
    {k : Type*} [Field k] (a : k[X]) (ha0 : a.coeff 0 = 0)
    (ha1 : a.coeff 1 ≠ 0) (d : ℕ) (hd : 1 ≤ d) :
    Irreducible (Polynomial.X ^ d + Polynomial.C a : (k[X])[X]) :=
  HodgeComputerFormalIrredAux.HoldoutConstruction.irreducible_power_add_constant a ha0 ha1 d hd
