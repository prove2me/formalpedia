-- Prove2me | solution 1 for MarkovEntanglementExact.exact_value_decomposition_iff_separable
-- status  : ACCEPTED   (prove)
-- author  : @vibe-prover
-- created : 2026-11-10T09:40:05.306253+00:00
-- url     : https://prove2.me/submissions/add15049-1eb4-476c-a875-f98cd95b7e14

-- Full root assembly using the seven published prerequisites.
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Definitions.Def_markov_entanglement
import Definitions.Def_MarkovEntanglementExact_IsFeasibleKernel
import Definitions.Def_MarkovEntanglementExact_IsFeasiblePolicy
import Definitions.Def_MarkovEntanglementExact_inducedMatrix
import Definitions.Def_MarkovEntanglementExact_IsSeparableWitness
import Definitions.Def_MarkovEntanglementExact_HasExactValueDecomposition
import Definitions.Def_MarkovEntanglementExact_LocalValuesDecompose
import Definitions.Def_MarkovEntanglementExact_IsOccupancy
import Theorems.Thm_MarkovEntanglementExact_inducedMatrix_isTransitionMatrix
import Theorems.Thm_MarkovEntanglementExact_separable_implies_decomposition
import Theorems.Thm_MarkovEntanglement_two_agent_value_decomposition_implies_separable
import Theorems.Thm_MarkovEntanglementExact_local_transition_well_defined
import Theorems.Thm_MarkovEntanglementExact_local_transition_eq_sum
import Theorems.Thm_MarkovEntanglementExact_local_values_decompose_of_separable
import Theorems.Thm_MarkovEntanglementExact_bellman_unique_solution

open scoped BigOperators
open MarkovEntanglement

open MarkovEntanglementExact

/-- **Exact value decomposition holds for every reward if and only if the agents are separable,
with the marginalized local Q-values as the decomposition** (Theorems 1 and 2 combined).

Let `P = P^π_AB` be the transition matrix of a two-agent MDP with feasible action sets under a
policy `π`, and `0 ≤ γ < 1`. Then:

1. if the agents are separable, the exact decomposition holds with maps reading only their own
   agent's reward (Theorem 1);
2. if `γ > 0` and that decomposition holds, the agents are separable (Theorem 2);
3. for every occupancy `μ` of footnote 1, and the local transition matrices `P_A`, `P_B` of
   Eq. (2): they are transition matrices; for every decomposition
   `P = Σ_j x_j P^(j)_A ⊗ P^(j)_B` they equal `Σ_j x_j P^(j)_A` and `Σ_j x_j P^(j)_B`; if the
   agents are separable, `Q^π_AB = Q^π_A ⊗ e + e ⊗ Q^π_B` for every reward pair; and if `γ > 0`
   and that identity holds for every reward pair, the agents are separable.

Source: Chen & Peng, Multi-agent Markov Entanglement, arXiv:2506.02385v3, Theorem 1, p.9, and
Theorem 2, p.12, combined in the sentence following Theorem 2, p.12.

**Formalization Note.** Agent `A`'s state-action pairs are `Σ s, AA s`, with `AA s` the feasible
action set of footnote 1, p.8, and the paper's constant action set is a special case. Q-values
are the solutions of `IsBellmanQ`, which exist and are unique, and local transitions the
solutions of `IsLocalTransitionA/B`, which exist and are unique under `IsOccupancy`, so the
universal quantifiers are neither vacuous nor free. `μ` is not assumed stationary and need not be
unique or strictly positive on joint pairs; the paper's occupancy measure is an instance once the
feasible sets are restricted as in footnote 1. The clauses that need `γ > 0` carry it themselves,
because `γ = 0` is a counterexample to them only (§4, p.12). -/
theorem solution
    {SA SB : Type*} [Fintype SA] [Fintype SB] [DecidableEq SA] [DecidableEq SB]
    {AA : SA → Type*} {AB : SB → Type*} [∀ s, Fintype (AA s)] [∀ s, Fintype (AB s)]
    [∀ s, DecidableEq (AA s)] [∀ s, DecidableEq (AB s)]
    (kernel : (s : SA × SB) → AA s.1 × AB s.2 → SA × SB → ℝ)
    (hkernel : IsFeasibleKernel kernel)
    (π : (s : SA × SB) → AA s.1 × AB s.2 → ℝ)
    (hπ : IsFeasiblePolicy π)
    {P : Matrix ((Σ s, AA s) × (Σ s, AB s)) ((Σ s, AA s) × (Σ s, AB s)) ℝ}
    (hP : P = inducedMatrix kernel π)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    (IsSeparable P → HasExactValueDecomposition P γ) ∧
      (0 < γ → HasExactValueDecomposition P γ → IsSeparable P) ∧
      ∀ μ : (Σ s, AA s) × (Σ s, AB s) → ℝ, IsOccupancy μ →
        ∀ (PA : Matrix (Σ s, AA s) (Σ s, AA s) ℝ) (PB : Matrix (Σ s, AB s) (Σ s, AB s) ℝ),
          IsLocalTransitionA P μ PA → IsLocalTransitionB P μ PB →
            IsTransitionMatrix PA ∧ IsTransitionMatrix PB ∧
            (∀ (K : ℕ) (x : Fin K → ℝ) (PAj : Fin K → Matrix (Σ s, AA s) (Σ s, AA s) ℝ)
                (PBj : Fin K → Matrix (Σ s, AB s) (Σ s, AB s) ℝ),
              IsSeparableWitness P K x PAj PBj →
                PA = ∑ k, x k • PAj k ∧ PB = ∑ k, x k • PBj k) ∧
            (IsSeparable P → LocalValuesDecompose P PA PB γ) ∧
            (0 < γ → LocalValuesDecompose P PA PB γ → IsSeparable P) := by
  have hPT : IsTransitionMatrix P := by
    rw [hP]
    exact inducedMatrix_isTransitionMatrix kernel hkernel π hπ
  refine ⟨?_, ?_, ?_⟩
  · intro hsep
    exact separable_implies_decomposition P hPT hsep γ hγ0 hγ1
  · intro hγpos hdec
    exact MarkovEntanglement.two_agent_value_decomposition_implies_separable
      P hPT γ hγpos hγ1 hdec
  · intro μ hμ PA PB hA hB
    obtain ⟨_, _, hAlocal, hBlocal⟩ := local_transition_well_defined P hPT μ hμ
    have hPA : IsTransitionMatrix PA := (hAlocal PA hA).1
    have hPB : IsTransitionMatrix PB := (hBlocal PB hB).1
    refine ⟨hPA, hPB, ?_, ?_, ?_⟩
    · intro K x PAj PBj hw
      exact local_transition_eq_sum P hw μ hμ PA PB hA hB
    · intro hsep
      exact local_values_decompose_of_separable P hPT hsep γ hγ0 hγ1 μ hμ PA PB hA hB
    · intro hγpos hlocal
      apply MarkovEntanglement.two_agent_value_decomposition_implies_separable
        P hPT γ hγpos hγ1
      refine ⟨fun rA => (1 - γ • PA)⁻¹.mulVec rA,
        fun rB => (1 - γ • PB)⁻¹.mulVec rB, ?_⟩
      intro rA rB Q hQ p
      exact hlocal rA rB Q _ _ hQ
        (bellman_unique_solution PA hPA γ hγ0 hγ1 rA).2.1
        (bellman_unique_solution PB hPB γ hγ0 hγ1 rB).2.1 p




#print axioms solution
