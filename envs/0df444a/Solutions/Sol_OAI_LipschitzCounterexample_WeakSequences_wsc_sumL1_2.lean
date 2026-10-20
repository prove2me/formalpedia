-- Prove2me | solution 2 for OAI.LipschitzCounterexample.WeakSequences.wsc_sumL1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T20:54:25.749532+00:00
-- url     : https://prove2.me/submissions/fe66ae08-5c7f-409e-b704-1c18b05ea25f

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzEquivalence/WeakSums.lean:L275-L332
-- (upload_full_project.md Phase 4): solution for node OAI.LipschitzCounterexample.WeakSequences.wsc_sumL1. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_LipschitzEquivalence
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FreeSpace
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_NullSequences
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeightedGraph
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Schur
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeakSums
import Theorems.Thm_OAI_LipschitzCounterexample_WeakSequences_uniform_tails_of_weakCauchy

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

theorem WeakCauchy.map {u : ℕ → E} (hu : WeakCauchy u) (T : E →L[ℝ] F) :
    WeakCauchy (fun n => T (u n)) := fun f => hu (f.comp T)

theorem WeakCauchy.bounded {u : ℕ → E} (hu : WeakCauchy u) :
    ∃ C : ℝ, ∀ n, ‖u n‖ ≤ C := by
  obtain ⟨C, hC⟩ := banach_steinhaus (g := fun n => NormedSpace.inclusionInDoubleDual ℝ E (u n))
    (fun f => by
      obtain ⟨C, hC⟩ := (hu f).isBounded_range.exists_norm_le
      exact ⟨C, fun n => hC _ ⟨n, rfl⟩⟩)
  refine ⟨C, fun n => ?_⟩
  have h := (NormedSpace.inclusionInDoubleDualLi ℝ).norm_map (u n)
  exact h ▸ hC n

variable {G : ℕ → Type uG} [∀ i, NormedAddCommGroup (G i)] [∀ i, NormedSpace ℝ (G i)]

theorem tendsto_tailL1 (x : SumL1 G) : Tendsto (fun N => tailL1 N x) atTop (𝓝 0) := by
  have hh : Tendsto (fun N => headL1 N x) atTop (𝓝 x) := by
    simp_rw [headL1_eq_sum]
    exact (lp.hasSum_single (by simp) x).tendsto_sum_nat
  simpa [tailL1] using (tendsto_const_nhds (x := x)).sub hh

theorem norm_tailL1_antitone (x : SumL1 G) : Antitone (fun N => ‖tailL1 N x‖) := by
  intro n m hnm
  dsimp only
  rw [sumL1_norm, sumL1_norm]
  apply Summable.tsum_le_tsum _ (sumL1_summable _) (sumL1_summable _)
  intro i
  simp only [tailL1_apply]
  split_ifs <;> simp_all
  all_goals omega

theorem finite_norm_le_of_weak_limits (v : ℕ → ∀ i, G i) (y : ∀ i, G i)
    (hy : ∀ i (f : G i →L[ℝ] ℝ), Tendsto (fun n => f (v n i)) atTop (𝓝 (f (y i))))
    (s : Finset ℕ) (C : ℝ) (hb : ∀ n, ∑ i ∈ s, ‖v n i‖ ≤ C) :
    ∑ i ∈ s, ‖y i‖ ≤ C := by
  choose f hf hfval using fun i => exists_dual_vector'' ℝ (y i)
  have ht : Tendsto (fun n => ∑ i ∈ s, f i (v n i)) atTop (𝓝 (∑ i ∈ s, ‖y i‖)) := by
    simpa [hfval] using tendsto_finsetSum s (fun i _ => hy i (f i))
  apply le_of_tendsto ht
  filter_upwards [] with n
  apply le_trans _ (hb n)
  apply Finset.sum_le_sum
  intro i hi
  calc
    f i (v n i) ≤ ‖f i (v n i)‖ := le_abs_self _
    _ ≤ ‖v n i‖ := by simpa using (f i).le_of_opNorm_le (hf i) (v n i)

theorem wsc_sumL1 (hG : ∀ i, WeakSequentiallyComplete (G i)) :
    WeakSequentiallyComplete (SumL1 G) := by
  intro u hu
  have hcoord (i : ℕ) : WeakCauchy (fun k => u k i) := hu.map (lp.evalCLM ℝ G 1 i)
  choose y hy using fun i => hG i (fun k => u k i) (hcoord i)
  obtain ⟨C, hC⟩ := hu.bounded
  have hfinite (s : Finset ℕ) : ∑ i ∈ s, ‖y i‖ ≤ C := by
    apply finite_norm_le_of_weak_limits (fun k i => u k i) y hy s C
    intro k
    apply le_trans _ (hC k)
    rw [sumL1_norm]
    exact (sumL1_summable (u k)).sum_le_tsum s (fun i hi => norm_nonneg _)
  have hsummable : Summable (fun i => ‖y i‖) :=
    summable_of_sum_le (fun i => norm_nonneg _) hfinite
  let x : SumL1 G := ⟨y, memℓp_gen (by simpa using hsummable)⟩
  refine ⟨x, fun f => ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hden : 0 < 3 * (‖f‖ + 1) := by positivity
  let δ := ε / (3 * (‖f‖ + 1))
  have hδ : 0 < δ := div_pos hε hden
  obtain ⟨N₁, hN₁⟩ := uniform_tails_of_weakCauchy u hu δ hδ
  obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.1 (tendsto_tailL1 x) δ hδ
  let N := max N₁ N₂
  have hxN : ‖tailL1 N x‖ < δ := by
    simpa only [dist_zero_right] using hN₂ N (le_max_right _ _)
  have huN (k : ℕ) : ‖tailL1 N (u k)‖ < δ :=
    (norm_tailL1_antitone (u k) (le_max_left _ _)).trans_lt (hN₁ k)
  have hhead : Tendsto (fun k => f (headL1 N (u k))) atTop (𝓝 (f (headL1 N x))) := by
    simp only [headL1_eq_sum, map_sum]
    apply tendsto_finsetSum
    intro i hi
    exact hy i (f.comp (lp.singleContinuousLinearMap ℝ G 1 i))
  obtain ⟨m, hm⟩ := Metric.tendsto_atTop.1 hhead (ε/3) (by positivity)
  refine ⟨m, fun k hk => ?_⟩
  have hid : f (u k) - f x = (f (headL1 N (u k)) - f (headL1 N x)) +
      f (tailL1 N (u k)) - f (tailL1 N x) := by
    simp only [tailL1, sub_apply, ContinuousLinearMap.id_apply, map_sub]; ring
  have hsmall : ‖f‖ * δ < ε/3 := by
    calc
      ‖f‖ * δ < (‖f‖ + 1) * δ := mul_lt_mul_of_pos_right (lt_add_one _) hδ
      _ = ε/3 := by dsimp [δ]; field_simp
  have h₁ : ‖f (tailL1 N (u k))‖ < ε/3 := by
    calc
      ‖f (tailL1 N (u k))‖ ≤ ‖f‖ * ‖tailL1 N (u k)‖ := f.le_opNorm _
      _ ≤ ‖f‖ * δ := mul_le_mul_of_nonneg_left (huN k).le (norm_nonneg _)
      _ < ε/3 := hsmall
  have h₂ : ‖f (tailL1 N x)‖ < ε/3 := by
    calc
      ‖f (tailL1 N x)‖ ≤ ‖f‖ * ‖tailL1 N x‖ := f.le_opNorm _
      _ ≤ ‖f‖ * δ := mul_le_mul_of_nonneg_left hxN.le (norm_nonneg _)
      _ < ε/3 := hsmall
  rw [dist_eq_norm, hid]
  apply (norm_sub_le _ _).trans_lt
  have h₃ := norm_add_le (f (headL1 N (u k)) - f (headL1 N x)) (f (tailL1 N (u k)))
  have h₄ := hm k hk
  rw [dist_eq_norm] at h₄
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


theorem solution.{uG} : type_of% @_root_.OAI.LipschitzCounterexample.WeakSequences.wsc_sumL1.{uG} := @_root_.OAI.LipschitzCounterexample.WeakSequences.wsc_sumL1.{uG}
