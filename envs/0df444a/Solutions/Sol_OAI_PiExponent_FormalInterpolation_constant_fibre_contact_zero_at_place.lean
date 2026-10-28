-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.constant_fibre_contact_zero_at_place
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T06:46:10.765782+00:00
-- url     : https://prove2.me/submissions/067dd733-0c4e-4c8e-95b8-07e7b4d38acd

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics
import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem solution
    {m K : Nat} (c : Fin K → Fin m → Complex)
    (T : Fin m → Nat) (e : Fin (m + 1) → Nat)
    (E : Type) [Field E] [Algebra Complex E] [Algebra.EssFiniteType Complex E]
    (x : Fin (m + 1) → E) (hfibre : x 0 = 1)
    (i0 : Fin m) (a : Complex) (ha : x i0.succ = algebraMap Complex E a)
    (hn : ∀ j : Fin K, c j i0 ≠ a)
    (nu : PolynomialCurvePlace E)
    (h_aff : ∀ i, (0 : WithTop Int) ≤ nu.1 (x i)) :
    polynomialCurveIdealContact nu x (logarithmicCentersIdeal c T e) = 0 := by
  classical
  rw [polynomialCurveIdealContact, if_pos h_aff]
  have htrunc0 : ∀ t : Nat, (InterpolationMatrix.truncatedLog t).coeff 0 = 0 := by
    intro t
    simp [InterpolationMatrix.truncatedLog, PowerSeries.coeff_trunc, PowerSeries.coeff_log]
  have haeval_trunc0 : ∀ t : Nat,
      Polynomial.aeval (0 : E) (InterpolationMatrix.truncatedLog t) = 0 := by
    intro t
    have h :=
      Polynomial.coeff_zero_eq_aeval_zero' (A := E) (InterpolationMatrix.truncatedLog t)
    simpa [htrunc0 t, map_zero] using h.symm
  set oneP : MvPolynomial (Fin (m + 1)) Complex := 1
  set X0m1 : MvPolynomial (Fin (m + 1)) Complex :=
    MvPolynomial.X (0 : Fin (m + 1)) - oneP
  have hx01 : MvPolynomial.aeval x X0m1 = 0 := by
    simp [X0m1, oneP, hfibre]
  have hgen_eval : ∀ j : Fin K,
      MvPolynomial.aeval x (logarithmicCoordinate (c j) T i0.succ) =
        algebraMap Complex E (a - c j i0) := by
    intro j
    have hxcoord :
        logarithmicCoordinate (c j) T i0.succ =
          MvPolynomial.X i0.succ - MvPolynomial.C (c j i0) -
            Polynomial.aeval X0m1 (InterpolationMatrix.truncatedLog (T i0)) := by
      simp [logarithmicCoordinate, X0m1, oneP]
    rw [hxcoord, map_sub, map_sub, MvPolynomial.aeval_X, MvPolynomial.aeval_C, ha]
    have hlog :
        MvPolynomial.aeval x
            (Polynomial.aeval X0m1 (InterpolationMatrix.truncatedLog (T i0))) = 0 := by
      -- aeval (f y) p = f (aeval y p), so f (aeval y p) = aeval (f y) p
      rw [← Polynomial.aeval_algHom_apply (MvPolynomial.aeval (R := Complex) x) X0m1
          (InterpolationMatrix.truncatedLog (T i0))]
      rw [hx01, haeval_trunc0]
    rw [hlog, sub_zero, ← map_sub]
  have hgen_pow : ∀ j : Fin K,
      MvPolynomial.aeval x (logarithmicCoordinate (c j) T i0.succ ^ e i0.succ) =
        algebraMap Complex E ((a - c j i0) ^ e i0.succ) := by
    intro j
    rw [map_pow, hgen_eval j, ← map_pow]
  have hmem_center : ∀ j : Fin K,
      logarithmicCoordinate (c j) T i0.succ ^ e i0.succ ∈
        logarithmicCenterIdeal (c j) T e := by
    intro j
    exact Ideal.subset_span ⟨i0.succ, rfl⟩
  set G := (∏ j : Fin K, logarithmicCoordinate (c j) T i0.succ ^ e i0.succ)
  have hGmem : G ∈ logarithmicCentersIdeal c T e := by
    simpa [G, logarithmicCentersIdeal] using
      Ideal.prod_mem_prod (fun j _ => hmem_center j)
  have hGeval :
      MvPolynomial.aeval x G =
        algebraMap Complex E (∏ j : Fin K, (a - c j i0) ^ e i0.succ) := by
    simp only [G, map_prod]
    exact Finset.prod_congr rfl fun j _ => hgen_pow j
  have hprod_ne : (∏ j : Fin K, (a - c j i0) ^ e i0.succ) ≠ 0 := by
    intro hz
    rcases Finset.prod_eq_zero_iff.mp hz with ⟨j, _, hj0⟩
    have he0 : e i0.succ ≠ 0 := fun he => by simp [he] at hj0
    have : a - c j i0 = 0 := (pow_eq_zero_iff he0).1 hj0
    exact hn j (sub_eq_zero.mp this).symm
  have hord0 : nu.1 (MvPolynomial.aeval x G) = ((0 : Int) : WithTop Int) := by
    have h := nu.property.1 _ hprod_ne
    simpa [hGeval] using h
  rw [Nat.sInf_eq_zero]
  refine Or.inl ?_
  refine ⟨G, hGmem, ?_⟩
  simpa using hord0
