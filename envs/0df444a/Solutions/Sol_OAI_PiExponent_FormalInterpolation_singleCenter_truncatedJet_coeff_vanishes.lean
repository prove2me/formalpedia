-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.singleCenter_truncatedJet_coeff_vanishes
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T12:33:32.898123+00:00
-- url     : https://prove2.me/submissions/4c163f9d-b003-48d5-a77c-556320b4dde3

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Tactic.Ring
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_variablePowerIdeal_pow_support

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

private theorem solution_jet_coordinate {m : Nat} (c : Fin m → Complex)
    (T : Fin m → Nat) (i : Fin (m + 1)) :
    truncatedPolynomialJet c T (logarithmicCoordinate c T i) = MvPolynomial.X i := by
  have hz : truncatedPolynomialJet c T (MvPolynomial.X 0 - 1) = MvPolynomial.X 0 := by
    simp only [truncatedPolynomialJet, map_sub, map_one, MvPolynomial.aeval_X,
      Fin.cases_zero]
    ring
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa only [logarithmicCoordinate, Fin.cases_zero] using hz
  · change truncatedPolynomialJet c T
      (MvPolynomial.X j.succ - MvPolynomial.C (c j) -
        Polynomial.aeval (MvPolynomial.X 0 - 1)
          (InterpolationMatrix.truncatedLog (T j))) = MvPolynomial.X j.succ
    have hp := (Polynomial.aeval_algHom_apply (truncatedPolynomialJet c T)
      (MvPolynomial.X 0 - 1) (InterpolationMatrix.truncatedLog (T j))).symm
    rw [hz] at hp
    rw [map_sub, map_sub, hp]
    simp only [truncatedPolynomialJet, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
      Fin.cases_succ, MvPolynomial.algebraMap_eq]
    ring

theorem solution {m : Nat} (v0 theta : Real) (w : Fin m → Real) (R : Real)
    (e : Fin (m + 1) → Nat) (T : Fin m → Nat) (c : Fin m → Complex)
    (hR : 0 < R) (he : ∀ i, 0 < e i)
    (hscale : ∀ i, R = (e i : Real) * InterpolationMatrix.rowWeights v0 theta w i)
    (n : Nat) (F : MvPolynomial (Fin (m + 1)) Complex)
    (hF : F ∈ logarithmicCenterIdeal c T e ^ n)
    (a : Fin (m + 1) → Nat)
    (ha : a ∈ OAI.PiExponent.strictWeightedSimplex
      (InterpolationMatrix.rowWeights v0 theta w) ((n : Real) * R)) :
    (truncatedPolynomialJet c T F).coeff (InterpolationMatrix.exponentVector a) = 0 := by
  classical
  let J : Ideal (MvPolynomial (Fin (m + 1)) Complex) :=
    Ideal.span (Set.range (fun i : Fin (m + 1) =>
      (MvPolynomial.X i : MvPolynomial (Fin (m + 1)) Complex) ^ e i))
  have hJ : Ideal.map (truncatedPolynomialJet c T) (logarithmicCenterIdeal c T e) ≤ J := by
    apply Ideal.map_le_iff_le_comap.mpr
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change truncatedPolynomialJet c T (logarithmicCoordinate c T i ^ e i) ∈ J
    rw [map_pow, solution_jet_coordinate]
    exact Ideal.subset_span ⟨i, rfl⟩
  have hmapped : truncatedPolynomialJet c T F ∈
      (Ideal.map (truncatedPolynomialJet c T) (logarithmicCenterIdeal c T e)) ^ n := by
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem (truncatedPolynomialJet c T) hF
  have hmem : truncatedPolynomialJet c T F ∈ J ^ n :=
    Ideal.pow_right_mono hJ n hmapped
  have hw : ∀ i, 0 ≤ InterpolationMatrix.rowWeights v0 theta w i := by
    intro i
    by_contra hneg
    have hnonpos := mul_nonpos_of_nonneg_of_nonpos
      (Nat.cast_nonneg (e i) : (0 : Real) ≤ (e i : Real))
      (le_of_lt (lt_of_not_ge hneg))
    rw [← hscale i] at hnonpos
    exact (not_le_of_gt hR) hnonpos
  have halt : ∑ i, InterpolationMatrix.rowWeights v0 theta w i * (a i : Real) <
      (n : Real) * R := (Finset.mem_filter.mp ha).2
  by_contra hne
  obtain ⟨b, hb, hba⟩ :=
    OAI.PiExponent.FormalInterpolation.variablePowerIdeal_pow_support
      e n (truncatedPolynomialJet c T F) hmem (InterpolationMatrix.exponentVector a) hne
  have hbR : (∑ i, (b i : Real)) = (n : Real) := by
    simpa only [Nat.cast_sum] using congrArg (fun k : Nat => (k : Real)) hb
  have hbaR : ∀ i, (e i : Real) * (b i : Real) ≤ (a i : Real) := by
    intro i
    have hnat : e i * b i ≤ a i := by
      simpa [InterpolationMatrix.exponentVector] using hba i
    simpa only [Nat.cast_mul] using
      (show ((e i * b i : Nat) : Real) ≤ (a i : Real) from Nat.cast_le.mpr hnat)
  have hlow : (n : Real) * R ≤
      ∑ i, InterpolationMatrix.rowWeights v0 theta w i * (a i : Real) := by
    calc
      (n : Real) * R = (∑ i, (b i : Real)) * R := by rw [hbR]
      _ = ∑ i, (b i : Real) * R := by rw [Finset.sum_mul]
      _ = ∑ i, InterpolationMatrix.rowWeights v0 theta w i *
          ((e i : Real) * (b i : Real)) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hscale i]
        ring
      _ ≤ ∑ i, InterpolationMatrix.rowWeights v0 theta w i * (a i : Real) :=
        Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hbaR i) (hw i))
  exact (not_lt_of_ge hlow) halt