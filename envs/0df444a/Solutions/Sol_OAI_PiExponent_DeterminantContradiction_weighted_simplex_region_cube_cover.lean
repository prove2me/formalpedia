-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.weighted_simplex_region_cube_cover
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-17T03:04:00.984886+00:00
-- url     : https://prove2.me/submissions/68721252-edd9-4c0b-9cbd-f34ab3e33048

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData
import Definitions.Def_OAI_NumberTheory_PiExponent_WeightedSimplexRegion

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.LiteralAnalytic

theorem solution
    (m : ℕ) (w : Fin m → ℝ) (T : ℝ)
    (hw : ∀ i, 0 < w i) (hT : 0 ≤ T) :
    weightedSimplexRegion w T ⊆ {x : Fin m → ℝ | ∃ a ∈ OAI.PiExponent.realWeightedSimplex w T, ∀ i, (a i : ℝ) ≤ x i ∧ x i < (a i : ℝ) + 1} := by
  classical
  intro x hx
  simp only [weightedSimplexRegion, Set.mem_setOf_eq] at hx
  rcases hx with ⟨hx_nonneg, hx_sum⟩
  let a : Fin m → ℕ := fun i => ⌊x i⌋₊
  change ∃ b ∈ OAI.PiExponent.realWeightedSimplex w T,
    ∀ i, (b i : ℝ) ≤ x i ∧ x i < (b i : ℝ) + 1
  refine ⟨a, ?_, ?_⟩
  · simp only [OAI.PiExponent.realWeightedSimplex, Finset.mem_filter,
      Fintype.mem_piFinset, Finset.mem_range]
    constructor
    · intro i
      have hterm : w i * x i ≤ T := by
        have hsingle : w i * x i ≤ ∑ j, w j * x j :=
          Finset.single_le_sum
            (fun j hj => mul_nonneg (hw j).le (hx_nonneg j))
            (Finset.mem_univ i)
        exact hsingle.trans hx_sum
      have hbound : x i ≤ T / w i := by
        apply (le_div_iff₀ (hw i)).2
        nlinarith
      exact Nat.lt_succ_of_le (Nat.floor_mono hbound)
    · calc
        ∑ i, w i * (a i : ℝ) ≤ ∑ i, w i * x i := by
          apply Finset.sum_le_sum
          intro i hi
          exact mul_le_mul_of_nonneg_left (Nat.floor_le (hx_nonneg i)) (hw i).le
        _ ≤ T := hx_sum
  · intro i
    constructor
    · exact Nat.floor_le (hx_nonneg i)
    · exact Nat.lt_floor_add_one (x i)