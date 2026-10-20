-- Prove2me | solution 2 for OAI.LipschitzCounterexample.GraphObstruction.no_lower_of_coordinate_null
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T20:57:48.974665+00:00
-- url     : https://prove2.me/submissions/ac827a04-c296-407a-b0b7-97d11e2964e5

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzEquivalence/GraphObstruction.lean:L127-L189
-- (upload_full_project.md Phase 4): solution for node OAI.LipschitzCounterexample.GraphObstruction.no_lower_of_coordinate_null. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_LipschitzEquivalence
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FreeSpace
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_NullSequences
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeightedGraph
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Schur
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeakSums
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphObstruction

-- ---- from OAI.Analysis.LipschitzEquivalence.GraphObstruction ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

universe uH uA uB

noncomputable section
namespace LipschitzCounterexample

namespace GraphObstruction
open Filter Topology
open WeakSequences
open scoped ENNReal NNReal
variable {H : Type uH} [NormedAddCommGroup H] [NormedSpace ℝ H]
theorem norm_sum_unitVector_sq (a : ℕ → ℕ) (ha : Function.Injective a) (N : ℕ) :
    ‖∑ j ∈ Finset.range N, unitVector (a j)‖ ^ 2 = (N : ℝ) := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [sum_inner, inner_sum, lp.inner_single_left]
  have hin (j k : ℕ) : inner ℝ (1 : ℝ) (unitVector (a k) (a j)) = if j = k then 1 else 0 := by
    simp [unitVector, lp.single_apply, Pi.single_apply, ha.eq_iff]
  simp only [hin]
  simp
  simpa only [Finset.card_range] using congrArg Finset.card (Finset.filter_eq_self.2 (fun i hi => Finset.mem_range.1 hi))

open NullSequences

omit [NormedSpace ℝ H] in
theorem eventually_trunc_small (y : ℕ → C0 (H := H))
    (hy : ∀ i, Tendsto (fun k => y k i) atTop (𝓝 0)) (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k in atTop, ‖NullSequences.trunc N (y k)‖ < ε := by
  have h : ∀ᶠ k in atTop, ∀ i ∈ Finset.range N, ‖y k i‖ < ε/2 := by
    apply (Finset.eventually_all _).2
    intro i hi
    simpa only [dist_zero_right] using (hy i).eventually (Metric.ball_mem_nhds _ (half_pos hε))
  filter_upwards [h] with k hk
  apply lt_of_le_of_lt ((NullSequences.norm_le (half_pos hε).le).2 ?_) (half_lt_self hε)
  intro i
  simp only [NullSequences.trunc_apply]
  split_ifs with hi
  · exact (hk i (Finset.mem_range.2 hi)).le
  · simpa using (half_pos hε).le

omit [NormedSpace ℝ H] in

theorem norm_sum_blocks_le (y : ℕ → C0 (H := H)) (n : ℕ → ℕ) (hn : StrictMono n)
    (C : ℝ) (hC : 0 ≤ C) (hy : ∀ j, ‖y j‖ ≤ C) (J : ℕ) :
    ‖∑ j ∈ Finset.range J, (NullSequences.trunc (n (j+1)) (y j) -
      NullSequences.trunc (n j) (y j))‖ ≤ C := by
  classical
  apply (NullSequences.norm_le hC).2
  intro i
  rw [NullSequences.sum_apply]
  let z := fun j => NullSequences.trunc (n (j+1)) (y j) - NullSequences.trunc (n j) (y j)
  have hi (j : ℕ) : z j i = if n j ≤ i ∧ i < n (j+1) then y j i else 0 := by
    change NullSequences.trunc (n (j+1)) (y j) i - NullSequences.trunc (n j) (y j) i = _
    simp only [NullSequences.trunc_apply]
    have h := hn (Nat.lt_succ_self j)
    split_ifs <;> simp_all
    all_goals omega
  change ‖∑ j ∈ Finset.range J, z j i‖ ≤ C
  by_cases hex : ∃ j ∈ Finset.range J, n j ≤ i ∧ i < n (j+1)
  · obtain ⟨j, hj, hij⟩ := hex
    rw [Finset.sum_eq_single j]
    · rw [hi, ite_eq_left hij]
      exact (norm_apply_le (y j) i).trans (hy j)
    · intro k hk hkj
      rw [hi, ite_eq_right]
      intro hik
      rcases lt_or_gt_of_ne hkj with hkj | hjk
      · have h := hn.monotone (Nat.succ_le_of_lt hkj)
        change n (k+1) ≤ n j at h
        omega
      · have h := hn.monotone (Nat.succ_le_of_lt hjk)
        change n (j+1) ≤ n k at h
        omega
    · exact fun h => (h hj).elim
  · have hz : ∀ j ∈ Finset.range J, z j i = 0 := by
      intro j hj
      rw [hi, ite_eq_right (fun h => hex ⟨j, hj, h⟩)]
    simpa only [Finset.sum_eq_zero hz, norm_zero] using hC

theorem no_lower_of_coordinate_null (T : RealL2 →L[ℝ] C0 (H := H))
    (hcoord : ∀ i, Tendsto (fun k => T (unitVector k) i) atTop (𝓝 0))
    (b : ℝ) (hb : 0 < b) (hlower : ∀ x, b * ‖x‖ ≤ ‖T x‖) : False := by
  classical
  let y : ℕ → C0 (H := H) := fun k => T (unitVector k)
  have hnorm (k : ℕ) : ‖y k‖ ≤ ‖T‖ := by
    simpa only [y, norm_unitVector, mul_one] using T.le_opNorm (unitVector k)
  have step (j : ℕ) (p : ℕ × ℕ) : ∃ q : ℕ × ℕ, p.1 < q.1 ∧ p.2 < q.2 ∧
      ‖y q.1 - (NullSequences.trunc q.2 (y q.1) - NullSequences.trunc p.2 (y q.1))‖ ≤
        WeightedGraph.weight j := by
    have hw := WeightedGraph.weight_pos j
    obtain ⟨K, hK⟩ := eventually_atTop.1 (eventually_trunc_small y hcoord p.2
      (WeightedGraph.weight j / 2) (half_pos hw))
    let k := max K (p.1+1)
    have hkh : ‖NullSequences.trunc p.2 (y k)‖ < WeightedGraph.weight j/2 :=
      hK k (le_max_left _ _)
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 (NullSequences.tendsto_trunc (y k))
      (WeightedGraph.weight j / 2) (half_pos hw)
    let n := max N (p.2+1)
    refine ⟨(k,n), (Nat.lt_succ_self _).trans_le (le_max_right _ _),
      (Nat.lt_succ_self _).trans_le (le_max_right _ _), ?_⟩
    have hkn := hN n (le_max_left _ _)
    rw [dist_eq_norm, norm_sub_rev] at hkn
    have he : y k - (NullSequences.trunc n (y k) - NullSequences.trunc p.2 (y k)) =
        (y k - NullSequences.trunc n (y k)) + NullSequences.trunc p.2 (y k) := by abel
    rw [he]
    exact (norm_add_le _ _).trans (by linarith)
  let next (j : ℕ) (p : ℕ × ℕ) := Classical.choose (step j p)
  let r : ℕ → ℕ × ℕ := fun j => Nat.rec (0,0) next j
  let k := fun j => (r (j+1)).1
  let n := fun j => (r j).2
  have hr (j : ℕ) : (r j).1 < (r (j+1)).1 ∧ n j < n (j+1) ∧
      ‖y (k j) - (NullSequences.trunc (n (j+1)) (y (k j)) -
        NullSequences.trunc (n j) (y (k j)))‖ ≤ WeightedGraph.weight j :=
    Classical.choose_spec (step j (r j))
  have hk : StrictMono k := strictMono_nat_of_lt_succ (fun j => (hr (j+1)).1)
  have hn : StrictMono n := strictMono_nat_of_lt_succ (fun j => (hr j).2.1)
  let z := fun j => NullSequences.trunc (n (j+1)) (y (k j)) - NullSequences.trunc (n j) (y (k j))
  have hbound (J : ℕ) : ‖T (∑ j ∈ Finset.range J, unitVector (k j))‖ ≤ ‖T‖ + 1 := by
    rw [map_sum]
    change ‖∑ j ∈ Finset.range J, y (k j)‖ ≤ _
    have hsplit : (∑ j ∈ Finset.range J, y (k j)) =
        (∑ j ∈ Finset.range J, z j) + ∑ j ∈ Finset.range J, (y (k j) - z j) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      abel
    rw [hsplit]
    apply (norm_add_le _ _).trans
    apply add_le_add
    · exact norm_sum_blocks_le (fun j => y (k j)) n hn ‖T‖ (by positivity) (fun j => hnorm (k j)) J
    · apply (norm_sum_le _ _).trans
      apply le_trans (Finset.sum_le_sum (fun j _ => (hr j).2.2))
      exact WeightedGraph.hasSum_weight.summable.sum_le_tsum _
        (fun _ _ => WeightedGraph.weight_nonneg _) |>.trans_eq WeightedGraph.hasSum_weight.tsum_eq
  obtain ⟨J, hJ⟩ := exists_nat_gt (((‖T‖+1)/b)^2)
  have hlow := hlower (∑ j ∈ Finset.range J, unitVector (k j))
  have hhi := hbound J
  have hnsq := norm_sum_unitVector_sq k hk.injective J
  have hnormle : ‖∑ j ∈ Finset.range J, unitVector (k j)‖ ≤ (‖T‖+1)/b :=
    (le_div_iff₀ hb).2 (by nlinarith)
  have hnonneg : 0 ≤ (‖T‖+1)/b := div_nonneg (by positivity) hb.le
  nlinarith [norm_nonneg (∑ j ∈ Finset.range J, unitVector (k j))]

variable {A : Type uA} {B : Type uB} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]

variable [CompleteSpace A] [CompleteSpace H]

end GraphObstruction

end LipschitzCounterexample
end

end OAI

-- ---- platform node ----
open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.GraphObstruction
open Filter Topology
open WeakSequences
open scoped ENNReal NNReal
open NullSequences


theorem solution.{uH} : type_of% @_root_.OAI.LipschitzCounterexample.GraphObstruction.no_lower_of_coordinate_null.{uH} := @_root_.OAI.LipschitzCounterexample.GraphObstruction.no_lower_of_coordinate_null.{uH}
