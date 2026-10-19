-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.logarithmicCenterIdeal_finiteDimensional
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T16:08:34.716001+00:00
-- url     : https://prove2.me/submissions/2f562b8e-c0c3-4015-bc2c-bf338923ad10

import Mathlib
import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
theorem pie_qint
    {m : Nat}
    (J : Ideal (MvPolynomial (Fin (m + 1)) Complex))
    (hcoord : ∀ i : Fin (m + 1),
      IsIntegral Complex (Ideal.Quotient.mk J (MvPolynomial.X i))) :
    Algebra.IsIntegral Complex ((MvPolynomial (Fin (m + 1)) Complex) ⧸ J) := by
  constructor
  intro a
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  refine MvPolynomial.induction_on (motive := fun p => IsIntegral Complex (Ideal.Quotient.mk J p)) p ?_ ?_ ?_
  · intro c
    have : Ideal.Quotient.mk J (MvPolynomial.C c) =
        algebraMap Complex ((MvPolynomial (Fin (m + 1)) Complex) ⧸ J) c := rfl
    rw [this]
    exact isIntegral_algebraMap
  · intro p q hp hq
    rw [map_add]
    exact hp.add hq
  · intro p i hp
    rw [map_mul]
    exact hp.mul (hcoord i)


theorem pie_aeval_int {A : Type*} [CommRing A] [Algebra Complex A] (x : A) (hx : IsIntegral Complex x)
    (L : Polynomial Complex) : IsIntegral Complex (Polynomial.aeval x L) := by
  induction L using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add]; exact hp.add hq
  | monomial n a =>
    rw [Polynomial.aeval_monomial]
    exact isIntegral_algebraMap.mul (hx.pow n)

theorem solution
    {m : Nat} (c : Fin m → Complex) (T : Fin m → Nat)
    (e : Fin (m + 1) → Nat) (he : ∀ i, 0 < e i) :
    FiniteDimensional Complex
      (MvPolynomial (Fin (m + 1)) Complex ⧸ logarithmicCenterIdeal c T e) := by
  set J := logarithmicCenterIdeal c T e with hJ
  have hnil : ∀ i, IsIntegral Complex (Ideal.Quotient.mk J (logarithmicCoordinate c T i)) := by
    intro i
    refine ⟨Polynomial.X ^ e i, Polynomial.monic_X_pow _, ?_⟩
    rw [Polynomial.eval₂_X_pow, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span ⟨i, rfl⟩
  have h0 : IsIntegral Complex (Ideal.Quotient.mk J (MvPolynomial.X 0)) := by
    have : Ideal.Quotient.mk J (MvPolynomial.X 0) = Ideal.Quotient.mk J (logarithmicCoordinate c T 0) + 1 := by
      simp [logarithmicCoordinate]
    rw [this]
    exact (hnil 0).add isIntegral_one
  have hint : ∀ i, IsIntegral Complex (Ideal.Quotient.mk J (MvPolynomial.X i)) := by
    intro i
    refine Fin.cases h0 (fun j => ?_) i
    have hL : Ideal.Quotient.mk J (Polynomial.aeval (MvPolynomial.X 0 - 1 : MvPolynomial (Fin (m + 1)) Complex)
        (InterpolationMatrix.truncatedLog (T j))) =
        Polynomial.aeval (Ideal.Quotient.mk J (MvPolynomial.X 0) - 1) (InterpolationMatrix.truncatedLog (T j)) := by
      rw [← Ideal.Quotient.mkₐ_eq_mk Complex]
      rw [show (Ideal.Quotient.mkₐ Complex J) (MvPolynomial.X 0) - 1 =
          (Ideal.Quotient.mkₐ Complex J) (MvPolynomial.X 0 - 1) by rw [map_sub, map_one],
        Polynomial.aeval_algHom_apply]
    have : Ideal.Quotient.mk J (MvPolynomial.X j.succ) =
        Ideal.Quotient.mk J (logarithmicCoordinate c T j.succ) + algebraMap Complex _ (c j) +
          Polynomial.aeval (Ideal.Quotient.mk J (MvPolynomial.X 0) - 1) (InterpolationMatrix.truncatedLog (T j)) := by
      rw [← hL]
      simp only [logarithmicCoordinate, Fin.cases_succ, map_sub]
      have : algebraMap Complex ((MvPolynomial (Fin (m + 1)) Complex) ⧸ J) (c j) =
          Ideal.Quotient.mk J (MvPolynomial.C (c j)) := rfl
      rw [this]
      ring
    rw [this]
    exact ((hnil _).add isIntegral_algebraMap).add (pie_aeval_int _ (h0.sub isIntegral_one) _)
  haveI : Algebra.IsIntegral Complex ((MvPolynomial (Fin (m + 1)) Complex) ⧸ J) := pie_qint J hint
  exact Algebra.IsIntegral.finite
