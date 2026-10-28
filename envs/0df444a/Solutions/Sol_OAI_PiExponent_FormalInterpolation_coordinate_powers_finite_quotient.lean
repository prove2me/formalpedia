-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.coordinate_powers_finite_quotient
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-24T09:11:50.763146+00:00
-- url     : https://prove2.me/submissions/0f3c93e5-e1ca-4129-b1e2-7c1b469e7819

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic

open MvPolynomial

theorem solution
    {d : Nat} (J : Ideal (MvPolynomial (Fin d) Complex))
    (hpowers : ∀ i : Fin d, ∃ N : Nat, MvPolynomial.X i ^ N ∈ J) :
    Module.Finite Complex (MvPolynomial (Fin d) Complex ⧸ J) := by
  let Q := MvPolynomial (Fin d) Complex ⧸ J
  let q : MvPolynomial (Fin d) Complex →ₐ[Complex] Q :=
    Ideal.Quotient.mkₐ Complex J
  let x : Fin d → Q := fun i => q (MvPolynomial.X i)
  let T : Subalgebra Complex Q := Algebra.adjoin Complex (Set.range x)
  have hfinite : Module.Finite Complex T := by
    apply Algebra.finite_adjoin_of_finite_of_isIntegral (Set.finite_range x)
    intro y hy
    rcases hy with ⟨i, rfl⟩
    obtain ⟨N, hN⟩ := hpowers i
    have hzero : x i ^ N = 0 := by
      change (Ideal.Quotient.mk J (MvPolynomial.X i)) ^ N = 0
      rw [← map_pow]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hN
    have hpow : x i ^ (N + 1) = 0 := by
      simpa [pow_succ, hzero]
    exact IsIntegral.of_pow (Nat.zero_lt_succ N) (by
      simpa [hpow] using (isIntegral_zero : IsIntegral Complex (0 : Q)))
  have hgen : T = ⊤ := by
    change Algebra.adjoin Complex (Set.range x) = ⊤
    rw [Algebra.adjoin_range_eq_range_aeval]
    have hq : MvPolynomial.aeval x = q := by
      apply MvPolynomial.algHom_ext
      intro i
      simp [x]
    rw [hq]
    exact (AlgHom.range_eq_top q).mpr (Ideal.Quotient.mkₐ_surjective Complex J)
  letI : Module.Finite Complex T := hfinite
  let e : T ≃ₐ[Complex] (⊤ : Subalgebra Complex Q) :=
    T.equivOfEq (⊤ : Subalgebra Complex Q) hgen
  let e' : (⊤ : Subalgebra Complex Q) ≃ₐ[Complex] Q :=
    Subalgebra.topEquiv
  exact Module.Finite.equiv (e.trans e').toLinearEquiv