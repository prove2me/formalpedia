-- Prove2me | solution 1 for Kyprianou.ProofPreparation.eventually_prefix_eq_tsum_of_finite_support
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T03:02:09.309199+00:00
-- url     : https://prove2.me/submissions/064b80a1-4f15-4527-8b29-2d84041278aa

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory Filter Complex
open scoped NNReal ENNReal Nat Topology
set_option autoImplicit false


namespace Kyprianou.ProofPreparation

theorem eventually_prefix_eq_tsum_of_finite_support
    (N : ℕ → ℕ) (hfinite : Set.Finite {k : ℕ | N k ≠ 0}) :
    ∃ n : ℕ, ∀ m ≥ n,
      (∑' k, (N k : ENNReal)) =
        ∑ k ∈ Finset.range m, (N k : ENNReal) := by
  obtain ⟨n, hn⟩ := hfinite.bddAbove
  refine ⟨n + 1, fun m hm => ?_⟩
  apply tsum_eq_sum
  intro k hk
  simp only [Finset.mem_range, not_lt] at hk
  by_contra h
  have h' : N k ≠ 0 := by intro h0; apply h; simp [h0]
  have := hn h'
  omega

end Kyprianou.ProofPreparation

theorem solution
    (N : ℕ → ℕ) (hfinite : Set.Finite {k : ℕ | N k ≠ 0}) :
    ∃ n : ℕ, ∀ m ≥ n,
      (∑' k, (N k : ENNReal)) =
        ∑ k ∈ Finset.range m, (N k : ENNReal) := by
  first
  | exact Kyprianou.ProofPreparation.eventually_prefix_eq_tsum_of_finite_support
  | exact Kyprianou.ProofPreparation.eventually_prefix_eq_tsum_of_finite_support ..
  | (apply Kyprianou.ProofPreparation.eventually_prefix_eq_tsum_of_finite_support <;> assumption)
