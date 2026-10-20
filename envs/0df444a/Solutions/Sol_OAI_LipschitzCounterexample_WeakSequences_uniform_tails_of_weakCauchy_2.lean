-- Prove2me | solution 2 for OAI.LipschitzCounterexample.WeakSequences.uniform_tails_of_weakCauchy
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T20:52:39.777488+00:00
-- url     : https://prove2.me/submissions/59058dcf-a0a6-4b75-85d0-370b2190e093

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzEquivalence/WeakSums.lean:L183-L257
-- (upload_full_project.md Phase 4): solution for node OAI.LipschitzCounterexample.WeakSequences.uniform_tails_of_weakCauchy. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_LipschitzEquivalence
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FreeSpace
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_NullSequences
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeightedGraph
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Schur
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeakSums
import Theorems.Thm_OAI_LipschitzCounterexample_WeakSequences_schur_cauchy
import Theorems.Thm_OAI_LipschitzCounterexample_WeakSequences_uniform_tails_of_cauchy

-- ---- from OAI.Analysis.LipschitzEquivalence.WeakSums ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e

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

theorem exists_common_functionals (z : ℕ → SumL1 G)
    (hz : ∀ j k, j ≠ k → ∀ i, z j i = 0 ∨ z k i = 0) :
    ∃ f : ∀ i, G i →L[ℝ] ℝ, (∀ i, ‖f i‖ ≤ 1) ∧ ∀ j i, f i (z j i) = ‖z j i‖ := by
  classical
  let f : ∀ i, G i →L[ℝ] ℝ := fun i => if h : ∃ j, z j i ≠ 0 then
    Classical.choose (exists_dual_vector'' ℝ (z (Classical.choose h) i)) else 0
  refine ⟨f, ?_, ?_⟩
  · intro i
    by_cases hi : ∃ j, z j i ≠ 0
    · simp only [f, dite_eq_left hi]
      exact (Classical.choose_spec (exists_dual_vector'' ℝ (z (Classical.choose hi) i))).1
    · simp [f, hi]
  · intro j i
    by_cases hji : z j i = 0
    · simp [hji]
    · have hex : ∃ k, z k i ≠ 0 := ⟨j, hji⟩
      have heq : Classical.choose hex = j := by
        by_contra hne
        cases hz (Classical.choose hex) j hne i with
        | inl h => exact Classical.choose_spec hex h
        | inr h => exact hji h
      simp only [f, dite_eq_left hex, heq]
      exact (Classical.choose_spec (exists_dual_vector'' ℝ (z j i))).2

theorem uniform_tails_of_weakCauchy (u : ℕ → SumL1 G) (hu : WeakCauchy u)
    (ε : ℝ) (hε : 0 < ε) : ∃ N, ∀ k, ‖tailL1 N (u k)‖ < ε := by
  classical
  by_contra hn
  push Not at hn
  have chooseStep (n : ℕ) : ∃ q : ℕ × ℕ, n < q.1 ∧
      ε ≤ ‖tailL1 n (u q.2)‖ ∧ ‖tailL1 q.1 (u q.2)‖ < ε/2 := by
    obtain ⟨k, hk⟩ := hn n
    obtain ⟨m, hm⟩ := Metric.tendsto_atTop.1 (tendsto_tailL1 (u k)) (ε/2) (half_pos hε)
    refine ⟨(max m (n+1), k), ?_, hk, ?_⟩
    · exact (Nat.lt_succ_self n).trans_le (le_max_right _ _)
    · simpa only [dist_zero_right] using hm (max m (n+1)) (le_max_left _ _)
  let next (n : ℕ) := Classical.choose (chooseStep n)
  let n : ℕ → ℕ := fun j => Nat.rec 0 (fun _ p => (next p).1) j
  let a (j : ℕ) := (next (n j)).2
  have hr (j : ℕ) : n j < n (j+1) ∧ ε ≤ ‖tailL1 (n j) (u (a j))‖ ∧
      ‖tailL1 (n (j+1)) (u (a j))‖ < ε/2 := Classical.choose_spec (chooseStep (n j))
  have hmono : StrictMono n := strictMono_nat_of_lt_succ (fun j => (hr j).1)
  let z : ℕ → SumL1 G := fun j => headL1 (n (j+1)) (u (a j)) - headL1 (n j) (u (a j))
  have hzi (j i : ℕ) : z j i = @ite (G i) (n j ≤ i ∧ i < n (j+1))
      (Classical.propDecidable _) (u (a j) i) 0 := by
    change headL1 (n (j+1)) (u (a j)) i - headL1 (n j) (u (a j)) i = _
    simp only [headL1_apply]
    rcases Classical.em (i < n j) with hlo | hlo
    · have hhi : i < n (j+1) := hlo.trans (hr j).1
      rw [ite_eq_left hhi, ite_eq_left hlo, ite_eq_right (by omega)]
      exact sub_self _
    · rcases Classical.em (i < n (j+1)) with hhi | hhi
      · rw [ite_eq_left hhi, ite_eq_right hlo, ite_eq_left ⟨Nat.le_of_not_gt hlo, hhi⟩, sub_zero]
      · rw [ite_eq_right hhi, ite_eq_right hlo, ite_eq_right (by omega), sub_self]
  have hzlower (j : ℕ) : ε/2 < ‖z j‖ := by
    have hid : tailL1 (n j) (u (a j)) = z j + tailL1 (n (j+1)) (u (a j)) := by
      dsimp [z, tailL1]; simp only [sub_apply, ContinuousLinearMap.id_apply]; abel
    have hh := norm_add_le (z j) (tailL1 (n (j+1)) (u (a j)))
    rw [← hid] at hh
    linarith [(hr j).2.1, (hr j).2.2]
  have hdisj (j k : ℕ) (hjk : j ≠ k) (i : ℕ) : z j i = 0 ∨ z k i = 0 := by
    rcases Classical.em (n j ≤ i ∧ i < n (j+1)) with hj | hj
    · apply Or.inr
      have hk : ¬ (n k ≤ i ∧ i < n (k+1)) := by
        intro hk
        rcases lt_or_gt_of_ne hjk with hjk | hkj
        · have hm := hmono.monotone (Nat.succ_le_of_lt hjk)
          change n (j+1) ≤ n k at hm
          omega
        · have hm := hmono.monotone (Nat.succ_le_of_lt hkj)
          change n (k+1) ≤ n j at hm
          omega
      rw [hzi, ite_eq_right hk]
    · apply Or.inl
      rw [hzi, ite_eq_right hj]
  obtain ⟨f, hf, hfz⟩ := exists_common_functionals z hdisj
  let T := coordinateTests f hf
  have hnorm (j : ℕ) : ‖T (z j)‖ = ‖z j‖ := by
    rw [sumL1_norm, sumL1_norm]
    apply tsum_congr
    intro i
    change ‖f i (z j i)‖ = ‖z j i‖
    rw [hfz, norm_norm]
  have hle (j : ℕ) : ‖z j‖ ≤ ‖tailL1 (n j) (T (u (a j)))‖ := by
    rw [← hnorm, sumL1_norm, sumL1_norm]
    apply Summable.tsum_le_tsum _ (sumL1_summable _) (sumL1_summable _)
    intro i
    change ‖f i (z j i)‖ ≤ _
    rw [hzi, tailL1_apply]
    rcases Classical.em (n j ≤ i ∧ i < n (j+1)) with hi | hi
    · rw [ite_eq_left hi, ite_eq_left hi.1]
      exact le_rfl
    · rw [ite_eq_right hi, map_zero, norm_zero]
      exact norm_nonneg _
  obtain ⟨N, hN⟩ := uniform_tails_of_cauchy (fun k => T (u k))
    (schur_cauchy (hu.map T)) (ε/2) (half_pos hε)
  have ht : ‖tailL1 (n N) (T (u (a N)))‖ < ε/2 :=
    (norm_tailL1_antitone (T (u (a N))) (hmono.id_le N)).trans_lt (hN (a N))
  linarith [hle N, hzlower N]

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


theorem solution.{uG} : type_of% @_root_.OAI.LipschitzCounterexample.WeakSequences.uniform_tails_of_weakCauchy.{uG} := @_root_.OAI.LipschitzCounterexample.WeakSequences.uniform_tails_of_weakCauchy.{uG}
