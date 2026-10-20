-- Prove2me | solution 2 for OAI.LipschitzCounterexample.WeakSequences.schur_cauchy
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T20:49:31.576907+00:00
-- url     : https://prove2.me/submissions/42f061b3-c003-42e7-8087-748f4ebc8592

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzEquivalence/WeakSums.lean:L34-L52
-- (upload_full_project.md Phase 4): solution for node OAI.LipschitzCounterexample.WeakSequences.schur_cauchy. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_LipschitzEquivalence
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FreeSpace
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_NullSequences
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeightedGraph
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Schur
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeakSums
import Theorems.Thm_OAI_LipschitzCounterexample_WeakSequences_schur

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

theorem schur_cauchy {u : ℕ → RealL1} (hu : WeakCauchy u) : CauchySeq u := by
  by_contra hn
  rw [Metric.cauchySeq_iff] at hn
  push Not at hn
  obtain ⟨ε, hε, hn⟩ := hn
  choose a ha b hb hab using hn
  have hweak : WeakNull (fun n => u (a n) - u (b n)) := by
    intro f
    rw [Metric.tendsto_atTop]
    intro δ hδ
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 (hu f) δ hδ
    refine ⟨N, fun n hn => ?_⟩
    simpa only [map_sub, dist_zero_right, ← dist_eq_norm] using
      hN (a n) (hn.trans (ha n)) (b n) (hn.trans (hb n))
  have hlim := schur hweak
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hlim ε hε
  have h := hN N le_rfl
  rw [dist_zero_right, ← dist_eq_norm] at h
  exact (not_lt_of_ge (hab N)) h

variable {G : ℕ → Type uG} [∀ i, NormedAddCommGroup (G i)] [∀ i, NormedSpace ℝ (G i)]

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


theorem solution : type_of% @_root_.OAI.LipschitzCounterexample.WeakSequences.schur_cauchy := @_root_.OAI.LipschitzCounterexample.WeakSequences.schur_cauchy
