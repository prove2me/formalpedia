-- Prove2me | solution 1 for MonotonicSolutions.StrongMono.shapley_isStronglyMonotonic
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:29:26.086101+00:00
-- url     : https://prove2.me/submissions/2aab7bf3-806f-47f6-9acd-6f54f74ef055

import Mathlib
import Definitions.Def_Supermodularity_Cooperative_ShapleyValue
import Definitions.Def_MonotonicSolutions_StrongMono_Game
import Definitions.Def_MonotonicSolutions_StrongMono_Axioms

namespace MonotonicSolutions.StrongMono

theorem aux_shsm_marginal_eq {n : ℕ} (v : Finset (Fin n) → ℝ) (i : Fin n)
    (S : Finset (Fin n)) (hS : S ∈ (Finset.univ.erase i).powerset) :
    v (insert i S) - v S = marginal v i S := by
  have hi : i ∉ S := by
    intro h
    have := Finset.mem_powerset.mp hS h
    simp at this
  simp [marginal, hi]

end MonotonicSolutions.StrongMono

open MonotonicSolutions.StrongMono

theorem solution {n : ℕ} :
    IsStronglyMonotonic (fun v : Game n => Supermodularity.Cooperative.ShapleyValue v.1) := by
  intro v w i h
  unfold Supermodularity.Cooperative.ShapleyValue
  apply Finset.sum_le_sum
  intro S hS
  rw [aux_shsm_marginal_eq v.1 i S hS, aux_shsm_marginal_eq w.1 i S hS]
  apply mul_le_mul_of_nonneg_left (h S)
  positivity
