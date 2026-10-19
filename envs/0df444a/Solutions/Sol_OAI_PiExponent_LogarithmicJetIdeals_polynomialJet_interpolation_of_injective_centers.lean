-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.polynomialJet_interpolation_of_injective_centers
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T17:22:53.054829+00:00
-- url     : https://prove2.me/submissions/f4ec997d-5465-4594-bb80-98e8cbaba4b3

import Definitions.Def_OAI_PiExponent_PolynomialLogarithmicJets
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_polynomialJet_aeval_jetCoordinate
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_localJetIdeal_pairwise_isCoprime
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_coeff_polynomialJet_eq_zero_of_mem_localJetIdeal
import Mathlib.Data.Finsupp.Weight
import Mathlib.RingTheory.Ideal.Quotient.Operations

open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

theorem solution
    {m K : ℕ} (c : Fin K → Fin m → ℂ) (T : Fin m → ℕ)
    (e : Fin (m + 1) → ℕ) (he : ∀ i, 0 < e i)
    (hc : Function.Injective c) (k : ℕ)
    (f : Fin K → (Fin (m + 1) →₀ ℕ) → ℂ) :
    ∃ P : MvPolynomial (Fin (m + 1)) ℂ,
      ∀ j : Fin K, ∀ u : Fin (m + 1) →₀ ℕ,
        (∑ i, u i / e i) < k →
          MvPolynomial.coeff u (polynomialJet (c j) T P) = f j u := by
  classical
  let b : Fin (m + 1) → ℕ := fun i => k * e i + 1
  let N : ℕ := ∑ i, b i
  let S : Finset (Fin (m + 1) →₀ ℕ) :=
    (Finsupp.finite_of_degree_le (σ := Fin (m + 1)) N).toFinset
  let Q : Fin K → MvPolynomial (Fin (m + 1)) ℂ :=
    fun j => ∑ u ∈ S, MvPolynomial.monomial u (f j u)
  let R : Fin K → MvPolynomial (Fin (m + 1)) ℂ :=
    fun j => MvPolynomial.aeval (jetCoordinate (c j) T) (Q j)
  have hR (j : Fin K) : polynomialJet (c j) T (R j) = Q j :=
    polynomialJet_aeval_jetCoordinate (c j) T (Q j)
  have hcop : Pairwise (fun j l : Fin K =>
      IsCoprime (localJetIdeal (c j) T b) (localJetIdeal (c l) T b)) :=
    localJetIdeal_pairwise_isCoprime c T b (fun i => Nat.zero_lt_succ _) hc
  obtain ⟨P, hP⟩ := Ideal.exists_forall_sub_mem_ideal hcop R
  refine ⟨P, ?_⟩
  intro j u hu
  have hbound : ∀ i, u i < b i := by
    intro i
    have hterm : u i / e i ≤ ∑ a, u a / e a :=
      Finset.single_le_sum (fun a _ => Nat.zero_le (u a / e a)) (Finset.mem_univ i)
    have hdiv : u i / e i < k := lt_of_le_of_lt hterm hu
    have hlt : u i < k * e i := (Nat.div_lt_iff_lt_mul (he i)).mp hdiv
    change u i < k * e i + 1
    exact lt_trans hlt (Nat.lt_succ_self _)
  have hdeg : u.degree ≤ N := by
    change u.degree ≤ ∑ i, b i
    rw [Finsupp.degree_eq_sum]
    exact Finset.sum_le_sum (fun i _ => Nat.le_of_lt (hbound i))
  have hSu : u ∈ S := by
    change u ∈ (Finsupp.finite_of_degree_le (σ := Fin (m + 1)) N).toFinset
    rw [Set.Finite.mem_toFinset]
    exact hdeg
  have hQ : MvPolynomial.coeff u (Q j) = f j u := by
    simp [Q, MvPolynomial.coeff_sum, hSu]
  have hzero := coeff_polynomialJet_eq_zero_of_mem_localJetIdeal
    (c j) T b (P - R j) (hP j) u hbound
  rw [map_sub, MvPolynomial.coeff_sub, hR j, hQ] at hzero
  exact sub_eq_zero.mp hzero
