-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.bounded_support_representatives_of_monomials
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T13:25:23.362643+00:00
-- url     : https://prove2.me/submissions/944ca7ba-c078-4bfb-a29a-0ff4b0ce4691

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.RingTheory.Ideal.Quotient.Operations

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem solution
    {m : Nat}
    (J : Ideal (MvPolynomial (Fin (m + 1)) Complex))
    (N : Nat)
    (hmono : ∀ a : Fin (m + 1) →₀ Nat,
      ∃ R : MvPolynomial (Fin (m + 1)) Complex,
        (∀ b ∈ R.support, ∀ i : Fin (m + 1), b i < N) ∧
          MvPolynomial.monomial a (1 : Complex) - R ∈ J) :
    ∀ P : MvPolynomial (Fin (m + 1)) Complex,
      ∃ R : MvPolynomial (Fin (m + 1)) Complex,
        (∀ b ∈ R.support, ∀ i : Fin (m + 1), b i < N) ∧ P - R ∈ J := by
  classical
  intro P
  let rep : (Fin (m + 1) →₀ Nat) → MvPolynomial (Fin (m + 1)) Complex :=
    fun a => Classical.choose (hmono a)
  have hrep (a : Fin (m + 1) →₀ Nat) :
      (∀ b ∈ (rep a).support, ∀ i : Fin (m + 1), b i < N) ∧
        MvPolynomial.monomial a (1 : Complex) - rep a ∈ J :=
    Classical.choose_spec (hmono a)
  refine ⟨∑ a ∈ P.support, P.coeff a • rep a, ?_, ?_⟩
  · intro b hb i
    have hb' : b ∈ P.support.biUnion (fun a => (P.coeff a • rep a).support) :=
      MvPolynomial.support_sum hb
    obtain ⟨a, ha, hmem⟩ := Finset.mem_biUnion.mp hb'
    exact (hrep a).1 b (MvPolynomial.support_smul hmem) i
  · have hdecomp :
        P - (∑ a ∈ P.support, P.coeff a • rep a) =
          ∑ a ∈ P.support,
            (MvPolynomial.monomial a (P.coeff a) - P.coeff a • rep a) := by
      rw [Finset.sum_sub_distrib, MvPolynomial.support_sum_monomial_coeff]
    rw [hdecomp]
    apply J.sum_mem
    intro a ha
    have h := J.smul_of_tower_mem (P.coeff a) (hrep a).2
    simpa only [smul_sub, MvPolynomial.smul_monomial, smul_eq_mul, mul_one] using h
