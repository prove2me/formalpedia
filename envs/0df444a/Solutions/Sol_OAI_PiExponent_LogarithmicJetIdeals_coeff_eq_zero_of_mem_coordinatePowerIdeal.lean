-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.coeff_eq_zero_of_mem_coordinatePowerIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T18:30:50.882023+00:00
-- url     : https://prove2.me/submissions/efb59d4a-71ce-412a-89c5-d19c29bf36f7

import Definitions.Def_OAI_PiExponent_PolynomialLogarithmicJets

open OAI.PiExponent.LogarithmicJetIdeals

theorem solution
    {n : ℕ} (b : Fin n → ℕ) (Q : MvPolynomial (Fin n) ℂ)
    (hQ : Q ∈ Ideal.span (Set.range (fun i : Fin n => MvPolynomial.X i ^ b i) : Set (MvPolynomial (Fin n) ℂ)))
    (u : Fin n →₀ ℕ) (hu : ∀ i, u i < b i) :
    MvPolynomial.coeff u Q = 0 := by
  classical
  let P : MvPolynomial (Fin n) ℂ → Prop := fun R =>
    ∀ v : Fin n →₀ ℕ, (∀ i, v i < b i) → MvPolynomial.coeff v R = 0
  have hQ' : Q ∈ Submodule.span (MvPolynomial (Fin n) ℂ)
      (Set.range (fun i : Fin n => MvPolynomial.X i ^ b i)) := hQ
  have hP : P Q := by
    refine Submodule.span_induction (p := fun R _ => P R) ?_ ?_ ?_ ?_ hQ'
    · intro g hg
      rcases Set.mem_range.mp hg with ⟨i, rfl⟩
      intro v hv
      have hne : Finsupp.single i (b i) ≠ v := by
        intro heq
        have hval := congrArg (fun f : Fin n →₀ ℕ => f i) heq
        have hvEq : b i = v i := by simpa using hval
        exact (ne_of_lt (hv i)) hvEq.symm
      simp [MvPolynomial.coeff_X_pow, hne]
    · intro v hv
      simp
    · intro A B hA hB ihA ihB v hv
      simp [MvPolynomial.coeff_add, ihA v hv, ihB v hv]
    · intro a A hA ihA v hv
      rw [smul_eq_mul, MvPolynomial.coeff_mul]
      apply Finset.sum_eq_zero
      intro p hp
      have hp' : p.1 + p.2 = v :=
        Finset.HasAntidiagonal.mem_antidiagonal.mp hp
      have hright : ∀ i, p.2 i < b i := by
        intro i
        have hle : p.2 i ≤ v i := by
          rw [← hp']
          simp
        exact lt_of_le_of_lt hle (hv i)
      rw [ihA p.2 hright, mul_zero]
  exact hP u hu