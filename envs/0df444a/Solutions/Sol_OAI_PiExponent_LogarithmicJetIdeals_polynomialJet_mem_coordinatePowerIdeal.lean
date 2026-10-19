-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.polynomialJet_mem_coordinatePowerIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T18:36:30.084252+00:00
-- url     : https://prove2.me/submissions/dec7199f-ba45-42d8-a7b1-784223bd8f1f

import Definitions.Def_OAI_PiExponent_PolynomialLogarithmicJets
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Tactic.Ring

open OAI.PiExponent.LogarithmicJetIdeals

theorem solution
    {m : ℕ} (c : Fin m → ℂ) (T : Fin m → ℕ)
    (b : Fin (m + 1) → ℕ) (P : MvPolynomial (Fin (m + 1)) ℂ)
    (hP : P ∈ localJetIdeal c T b) :
    polynomialJet c T P ∈ Ideal.span
      (Set.range (fun i : Fin (m + 1) => MvPolynomial.X i ^ b i) :
        Set (MvPolynomial (Fin (m + 1)) ℂ)) := by
  let coordinatePowerIdeal : Ideal (MvPolynomial (Fin (m + 1)) ℂ) :=
    Ideal.span (Set.range (fun i : Fin (m + 1) =>
      MvPolynomial.X i ^ b i) : Set (MvPolynomial (Fin (m + 1)) ℂ))
  have hC (z : ℂ) :
      polynomialJet c T (MvPolynomial.C z) = MvPolynomial.C z := by
    simp [polynomialJet]
  have hzero :
      polynomialJet c T (MvPolynomial.X 0 - 1) = MvPolynomial.X 0 := by
    simp only [polynomialJet, map_sub, map_one, MvPolynomial.aeval_X,
      Fin.cases_zero]
    ring
  have heval (q : Polynomial ℂ) :
      polynomialJet c T
          (Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X 0 - 1) q) =
        Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X 0) q := by
    have hcomp : (polynomialJet c T).toRingHom.comp MvPolynomial.C =
        MvPolynomial.C := by
      apply RingHom.ext
      intro z
      exact hC z
    change (polynomialJet c T).toRingHom
        (Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X 0 - 1) q) = _
    rw [Polynomial.hom_eval₂, hcomp]
    change Polynomial.eval₂ MvPolynomial.C
        (polynomialJet c T (MvPolynomial.X 0 - 1)) q = _
    rw [hzero]
  have hcoord (i : Fin (m + 1)) :
      polynomialJet c T (jetCoordinate c T i) = MvPolynomial.X i := by
    cases i using Fin.cases with
    | zero =>
        simpa only [jetCoordinate, Fin.cases_zero] using hzero
    | succ i =>
        simp only [jetCoordinate, Fin.cases_succ]
        rw [map_sub, map_sub, hC, heval]
        simp only [polynomialJet, MvPolynomial.aeval_X, Fin.cases_succ]
        ring
  have hgen (i : Fin (m + 1)) :
      (polynomialJet c T).toRingHom (jetCoordinate c T i ^ b i) ∈
        coordinatePowerIdeal := by
    change polynomialJet c T (jetCoordinate c T i ^ b i) ∈ coordinatePowerIdeal
    rw [map_pow, hcoord i]
    exact Ideal.subset_span ⟨i, rfl⟩
  have hmap :
      Ideal.map (polynomialJet c T).toRingHom (localJetIdeal c T b) ≤
        coordinatePowerIdeal := by
    rw [Ideal.map_le_iff_le_comap, localJetIdeal, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact Ideal.mem_comap.mpr (hgen i)
  have hmem :
      polynomialJet c T P ∈
        Ideal.map (polynomialJet c T).toRingHom (localJetIdeal c T b) := by
    exact Ideal.mem_map_of_mem _ hP
  exact hmap hmem