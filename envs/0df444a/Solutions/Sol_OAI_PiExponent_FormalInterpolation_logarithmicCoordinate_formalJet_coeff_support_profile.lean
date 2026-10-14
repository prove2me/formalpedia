-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.logarithmicCoordinate_formalJet_coeff_support_profile
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-13T12:06:29.171392+00:00
-- url     : https://prove2.me/submissions/89ec29a2-002d-4d35-862c-04961eec0205

import Definitions.Def_OAI_PiExponent_LogarithmicCenterIdeals

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open scoped BigOperators

private theorem equiv_lift {m : Nat} (f : PowerSeries Complex) :
    MvPowerSeries.finSuccEquiv Complex m (FormalInterpolation.liftSeries m f) =
      PowerSeries.map MvPowerSeries.C f := by
  simp [FormalInterpolation.liftSeries]

private theorem equiv_aeval {m : Nat} (p : Polynomial Complex) :
    MvPowerSeries.finSuccEquiv Complex m
      (Polynomial.aeval (MvPowerSeries.X 0) p) =
        PowerSeries.map MvPowerSeries.C (p : PowerSeries Complex) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [map_add, hp, hq]
  | monomial n a =>
    simp [Polynomial.aeval_monomial, Polynomial.coe_monomial,
      PowerSeries.monomial_eq_C_mul_X_pow, map_mul, map_pow,
      MvPowerSeries.algebraMap_apply]

private theorem equiv_coordinate_succ {m : Nat} (c : Fin m → Complex)
    (T : Fin m → Nat) (k : Fin m) :
    MvPowerSeries.finSuccEquiv Complex m
      (FormalInterpolation.formalJet c (FormalInterpolation.logarithmicCoordinate c T k.succ)) =
        PowerSeries.C (MvPowerSeries.X k) +
          PowerSeries.map MvPowerSeries.C
            (PowerSeries.log Complex - (InterpolationMatrix.truncatedLog (T k) :
              PowerSeries Complex)) := by
  have heval (p : Polynomial Complex) :
      FormalInterpolation.formalJet c (Polynomial.aeval (MvPolynomial.X 0 - 1) p) =
        Polynomial.aeval (MvPowerSeries.X 0) p := by
    rw [← AlgHom.comp_apply, ← Polynomial.aeval_algHom]
    simp [FormalInterpolation.formalJet]
  simp only [FormalInterpolation.logarithmicCoordinate, Fin.cases_succ, map_sub, heval]
  simp only [FormalInterpolation.formalJet, MvPolynomial.aeval_X,
    MvPolynomial.aeval_C, Fin.cases_succ]
  simp only [map_add, MvPowerSeries.algebraMap_apply,
    MvPowerSeries.finSuccEquiv_C, MvPowerSeries.finSuccEquiv_X_succ,
    equiv_lift, equiv_aeval, Algebra.algebraMap_self_apply]
  abel

theorem solution
    {m : Nat} (c : Fin m -> Complex) (T : Fin m -> Nat)
    (i : Fin (m + 1)) (b : Fin (m + 1) -> Nat)
    (hcoeff : MvPowerSeries.coeff (InterpolationMatrix.exponentVector b)
      (FormalInterpolation.formalJet c
        (FormalInterpolation.logarithmicCoordinate c T i)) ≠ 0) :
    (i = 0 /\ b = fun j => if j = 0 then 1 else 0) \/
      (exists k : Fin m, i = k.succ /\
        b = fun j => if j = k.succ then 1 else 0) \/
      (exists k : Fin m, exists n : Nat, i = k.succ /\
        (b = fun j => if j = 0 then n else 0) /\ T k <= n) := by
  classical
  induction i using Fin.cases with
  | zero =>
    have hx : InterpolationMatrix.exponentVector b = Finsupp.single 0 1 := by
      by_contra hx
      apply hcoeff
      simp [FormalInterpolation.formalJet, FormalInterpolation.logarithmicCoordinate,
        MvPowerSeries.coeff_X, hx]
    left
    refine ⟨rfl, ?_⟩
    funext j
    simpa [InterpolationMatrix.exponentVector, Finsupp.single_apply, eq_comm] using
      congrArg (fun d => d j) hx
  | succ k =>
    let d := InterpolationMatrix.exponentVector b
    have hc : MvPowerSeries.coeff d.tail
        (PowerSeries.coeff (d 0)
          (PowerSeries.C (MvPowerSeries.X k) + PowerSeries.map MvPowerSeries.C
            (PowerSeries.log Complex - (InterpolationMatrix.truncatedLog (T k) :
              PowerSeries Complex)))) ≠ 0 := by
      rw [← equiv_coordinate_succ c T k, MvPowerSeries.coeff_coeff_finSuccEquiv,
        Finsupp.cons_tail]
      exact hcoeff
    simp only [map_add, PowerSeries.coeff_C, PowerSeries.coeff_map,
      MvPowerSeries.coeff_C] at hc
    by_cases hd : d = Finsupp.single k.succ 1
    · right; left
      refine ⟨k, rfl, ?_⟩
      funext j
      simpa [d, InterpolationMatrix.exponentVector, Finsupp.single_apply, eq_comm] using
        congrArg (fun d => d j) hd
    · have hshape : ¬ (d.tail = Finsupp.single k 1 ∧ d 0 = 0) := by
        intro h
        apply hd
        rw [← Finsupp.cons_tail d, Finsupp.cons_eq_single_succ_iff]
        exact h
      have hfirst : MvPowerSeries.coeff d.tail
          (if d 0 = 0 then (MvPowerSeries.X k : MvPowerSeries (Fin m) Complex)
            else 0) = 0 := by
        by_cases h0 : d 0 = 0
        · have ht : d.tail ≠ Finsupp.single k 1 := fun ht => hshape ⟨ht, h0⟩
          simp [h0, MvPowerSeries.coeff_X, ht]
        · simp [h0]
      rw [hfirst, zero_add] at hc
      have ht : d.tail = 0 := by
        by_contra ht
        simp [ht] at hc
      rw [if_pos ht] at hc
      have hn : T k ≤ d 0 := by
        by_contra hn
        have hlt : d 0 < T k := Nat.lt_of_not_ge hn
        apply hc
        simp [map_sub, Polynomial.coeff_coe, InterpolationMatrix.truncatedLog,
          PowerSeries.coeff_trunc, hlt]
      have hp : d = Finsupp.single 0 (d 0) := by
        rw [← Finsupp.cons_tail d, ht, Finsupp.cons_zero_eq_single_zero]
        simp
      right; right
      refine ⟨k, d 0, rfl, ?_, hn⟩
      funext j
      simpa [d, InterpolationMatrix.exponentVector, Finsupp.single_apply, eq_comm] using
        congrArg (fun d => d j) hp

