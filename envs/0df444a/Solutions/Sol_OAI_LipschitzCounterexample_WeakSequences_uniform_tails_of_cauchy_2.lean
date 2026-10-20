-- Prove2me | solution 2 for OAI.LipschitzCounterexample.WeakSequences.uniform_tails_of_cauchy
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T20:51:06.909096+00:00
-- url     : https://prove2.me/submissions/734a5694-624e-4c75-bc61-8590b78f654f

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzEquivalence/WeakSums.lean:L138-L157
-- (upload_full_project.md Phase 4): solution for node OAI.LipschitzCounterexample.WeakSequences.uniform_tails_of_cauchy. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_LipschitzEquivalence
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FreeSpace
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_NullSequences
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeightedGraph
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Schur
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeakSums

-- ---- from OAI.Analysis.LipschitzEquivalence.WeakSums ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uE uF uG

noncomputable section
namespace LipschitzCounterexample

namespace WeakSequences
open Filter Topology
open scoped ENNReal NNReal
variable {E : Type uE} {F : Type uF} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

variable {G : ℕ → Type uG} [∀ i, NormedAddCommGroup (G i)] [∀ i, NormedSpace ℝ (G i)]

theorem tendsto_tailL1 (x : SumL1 G) : Tendsto (fun N => tailL1 N x) atTop (𝓝 0) := by
  have hh : Tendsto (fun N => headL1 N x) atTop (𝓝 x) := by
    simp_rw [headL1_eq_sum]
    exact (lp.hasSum_single (by simp) x).tendsto_sum_nat
  simpa [tailL1] using (tendsto_const_nhds (x := x)).sub hh

theorem norm_tailL1_le (N : ℕ) (x : SumL1 G) : ‖tailL1 N x‖ ≤ ‖x‖ := by
  rw [sumL1_norm, sumL1_norm]
  apply Summable.tsum_le_tsum _ (sumL1_summable _) (sumL1_summable _)
  intro i
  rw [tailL1_apply]
  split_ifs <;> simp

theorem uniform_tails_of_cauchy (u : ℕ → SumL1 G) (hu : CauchySeq u)
    (ε : ℝ) (hε : 0 < ε) : ∃ N, ∀ k, ‖tailL1 N (u k)‖ < ε := by
  obtain ⟨m, hm⟩ := Metric.cauchySeq_iff.1 hu (ε/2) (half_pos hε)
  have hh : ∀ᶠ N in atTop, ∀ k ∈ Finset.range (m+1), ‖tailL1 N (u k)‖ < ε/2 := by
    rw [Filter.eventually_all_finset]
    intro k hk
    exact (NormedAddGroup.tendsto_nhds_zero.1 (tendsto_tailL1 (u k))) _ (half_pos hε)
  obtain ⟨N, hN⟩ := hh.exists
  refine ⟨N, fun k => ?_⟩
  by_cases hk : k ≤ m
  · exact (hN k (Finset.mem_range.2 (Nat.lt_succ_iff.2 hk))).trans (by linarith)
  · have hkm : m ≤ k := Nat.le_of_not_ge hk
    have hid : tailL1 N (u k) = tailL1 N (u k - u m) + tailL1 N (u m) := by
      rw [map_sub]; abel
    rw [hid]
    apply (norm_add_le _ _).trans_lt
    have h₁ := (norm_tailL1_le N (u k - u m)).trans_lt (by
      simpa [dist_eq_norm] using hm k hkm m le_rfl)
    have h₂ := hN m (Finset.mem_range.2 (Nat.lt_succ_self m))
    linarith

end WeakSequences

namespace WeakSequences
open Filter Topology
open scoped NNReal ENNReal
variable {E : Type uE} {F : Type uF} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

open NullSequences

end WeakSequences

end LipschitzCounterexample
end

end OAI

-- ---- platform node ----
open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.WeakSequences
open Filter Topology
open scoped ENNReal NNReal


theorem solution.{uG} : type_of% @_root_.OAI.LipschitzCounterexample.WeakSequences.uniform_tails_of_cauchy.{uG} := @_root_.OAI.LipschitzCounterexample.WeakSequences.uniform_tails_of_cauchy.{uG}
