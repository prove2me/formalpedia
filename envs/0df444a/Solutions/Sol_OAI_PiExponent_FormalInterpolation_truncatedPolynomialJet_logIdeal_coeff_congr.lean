-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.truncatedPolynomialJet_logIdeal_coeff_congr
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T22:49:20.307541+00:00
-- url     : https://prove2.me/submissions/65b9617f-049b-4c4f-876b-c4633aac2375

import Mathlib
import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.RingTheory.Ideal.Quotient.Operations

open OAI.PiExponent OAI.PiExponent.FormalInterpolation
theorem h41_jet_coord {m : Nat} (c : Fin m → Complex) (T : Fin m → Nat) (i : Fin (m + 1)) :
    truncatedPolynomialJet c T (logarithmicCoordinate c T i) = MvPolynomial.X i := by
  cases i using Fin.cases with
  | zero =>
    simp [truncatedPolynomialJet, logarithmicCoordinate]
  | succ i =>
    simp only [logarithmicCoordinate, Fin.cases_succ, map_sub]
    rw [← Polynomial.aeval_algHom_apply]
    simp [truncatedPolynomialJet]
    ring

theorem h41_jet_mem {m : Nat} (c : Fin m → Complex) (T : Fin m → Nat)
    (S : Fin (m + 1) → Nat) (P : MvPolynomial (Fin (m + 1)) Complex)
    (h : P ∈ logarithmicCenterIdeal c T S) :
    truncatedPolynomialJet c T P ∈ Ideal.span ((fun s => MvPolynomial.monomial s (1 : Complex)) ''
      Set.range (fun i => Finsupp.single i (S i))) := by
  have h1 : truncatedPolynomialJet c T P ∈
      Ideal.map (truncatedPolynomialJet c T) (logarithmicCenterIdeal c T S) :=
    Ideal.mem_map_of_mem _ h
  rw [logarithmicCenterIdeal, Ideal.map_span] at h1
  refine (Ideal.span_mono ?_) h1
  rintro x ⟨y, ⟨i, rfl⟩, rfl⟩
  refine ⟨Finsupp.single i (S i), ⟨i, rfl⟩, ?_⟩
  simp only [map_pow, h41_jet_coord, MvPolynomial.X_pow_eq_monomial]

theorem h41_jet_coeff_zero {m : Nat} (c : Fin m → Complex) (T : Fin m → Nat)
    (S : Fin (m + 1) → Nat) (P : MvPolynomial (Fin (m + 1)) Complex)
    (h : P ∈ logarithmicCenterIdeal c T S)
    (a : Fin (m + 1) → Nat) (ha : ∀ i, a i < S i) :
    (truncatedPolynomialJet c T P).coeff (InterpolationMatrix.exponentVector a) = 0 := by
  have h1 := h41_jet_mem c T S P h
  rw [MvPolynomial.mem_ideal_span_monomial_image] at h1
  by_contra hne
  obtain ⟨si, ⟨i, rfl⟩, hle⟩ := h1 _ (MvPolynomial.mem_support_iff.mpr hne)
  have := hle i
  simp [InterpolationMatrix.exponentVector] at this
  exact absurd (ha i) (not_lt.mpr this)

theorem solution
    {m : Nat} (c : Fin m → Complex) (T : Fin m → Nat)
    (S : Fin (m + 1) → Nat)
    (P Q : MvPolynomial (Fin (m + 1)) Complex)
    (h : P - Q ∈ logarithmicCenterIdeal c T S) :
    ∀ a : {a : Fin (m + 1) → Nat // ∀ i, a i < S i},
      (truncatedPolynomialJet c T P).coeff (InterpolationMatrix.exponentVector a.1) =
        (truncatedPolynomialJet c T Q).coeff (InterpolationMatrix.exponentVector a.1) := by
  intro a
  have := h41_jet_coeff_zero c T S (P - Q) h a.1 a.2
  rw [map_sub, MvPolynomial.coeff_sub, sub_eq_zero] at this
  exact this

