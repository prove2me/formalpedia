-- Prove2me | solution 1 for OAI.LipschitzCounterexample.WeakSequences.uniform_tails_of_cauchy
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T19:44:23.450725+00:00
-- url     : https://prove2.me/submissions/477af20e-1673-4a6d-8cab-f442ddb75bcb

import Mathlib
import Definitions.Def_LipschitzEquivalence
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FreeSpace
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_NullSequences
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeightedGraph
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Schur
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeakSums

open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.WeakSequences
universe uE uF uG
open Filter Topology
open scoped ENNReal NNReal
variable {E : Type uE} {F : Type uF} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {G : ℕ → Type uG} [∀ i, NormedAddCommGroup (G i)] [∀ i, NormedSpace ℝ (G i)]
theorem h50_tail_le (N : ℕ) (y : SumL1 G) : ‖tailL1 N y‖ ≤ ‖y‖ := by
  rw [sumL1_norm, sumL1_norm]
  apply Summable.tsum_le_tsum (fun i => ?_) (sumL1_summable (tailL1 N y)) (sumL1_summable y)
  rw [tailL1_apply]
  split_ifs <;> simp

theorem h50_tail_tendsto (y : SumL1 G) : Tendsto (fun N => ‖tailL1 N y‖) atTop (𝓝 0) := by
  have heq : ∀ N, ‖tailL1 N y‖ = ∑' i, ‖y (i + N)‖ := by
    intro N
    rw [sumL1_norm]
    rw [← (sumL1_summable (tailL1 N y)).sum_add_tsum_nat_add N]
    rw [Finset.sum_eq_zero (fun i hi => by
      rw [tailL1_apply, if_neg (by simp at hi; omega), norm_zero]), zero_add]
    congr 1
    funext i
    rw [tailL1_apply, if_pos (by omega)]
  simp_rw [heq]
  exact tendsto_sum_nat_add (fun i => ‖y i‖)

theorem solution (u : ℕ → SumL1 G) (hu : CauchySeq u)
    (ε : ℝ) (hε : 0 < ε) : ∃ N, ∀ k, ‖tailL1 N (u k)‖ < ε := by
  obtain ⟨M, hM⟩ := Metric.cauchySeq_iff'.mp hu (ε/2) (half_pos hε)
  have hev : ∀ᶠ N in atTop, ∀ k ∈ Finset.range (M+1), ‖tailL1 N (u k)‖ < ε/2 := by
    rw [Filter.eventually_all_finset]
    intro k _
    exact (h50_tail_tendsto (u k)).eventually (gt_mem_nhds (half_pos hε))
  obtain ⟨N, hN⟩ := hev.exists
  refine ⟨N, fun k => ?_⟩
  by_cases hk : k ≤ M
  · exact (hN k (Finset.mem_range.mpr (by omega))).trans (half_lt_self hε)
  · have h1 := hM k (by omega)
    rw [dist_eq_norm] at h1
    have h2 := hN M (Finset.mem_range.mpr (by omega))
    have h3 : tailL1 N (u k) = tailL1 N (u k - u M) + tailL1 N (u M) := by
      rw [map_sub]; abel
    rw [h3]
    calc _ ≤ ‖tailL1 N (u k - u M)‖ + ‖tailL1 N (u M)‖ := norm_add_le _ _
      _ ≤ ‖u k - u M‖ + ‖tailL1 N (u M)‖ := by gcongr; exact h50_tail_le _ _
      _ < ε/2 + ε/2 := add_lt_add h1 h2
      _ = ε := by ring

