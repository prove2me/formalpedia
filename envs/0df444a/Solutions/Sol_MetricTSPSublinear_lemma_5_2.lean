-- Prove2me | solution 1 for MetricTSPSublinear.lemma_5_2
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T04:05:59.71606+00:00
-- url     : https://prove2.me/submissions/bdca98d1-8355-4d60-948c-8b3d0b14bd24

import Mathlib
import Definitions.Def_DoublingMST_IsMetric
import Definitions.Def_MetricTSPSublinear_cutLP
import Definitions.Def_MetricTSPSublinear_hull
import Definitions.Def_MetricTSPSublinear_IsDominatedShortening
import Definitions.Def_DoublingMST_mstWeight
import Definitions.Def_DoublingMST_IsMSTOf
import Theorems.Thm_MetricTSPSublinear_lemma_4_4

open scoped Classical

open MetricTSPSublinear in
theorem solution {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : DoublingMST.IsMetric d) (E : Finset (Sym2 (Fin n)))
    (hE : DoublingMST.IsMSTOf d Finset.univ E) (w0 : Sym2 (Fin n) → ℝ) (hw0 : IsDominatedShortening d E w0)
    (S N : Finset (Fin n)) (θ : ℝ) (hstop : cutLP d (S ∪ N) - cutLP d S ≤ θ) :
    IsDominatedShortening d E (fun e => if e ∈ hull E (S ∪ N) \ hull E S then 0 else w0 e) ∧
      ∑ e ∈ E, w0 e - ∑ e ∈ E, (if e ∈ hull E (S ∪ N) \ hull E S then 0 else w0 e) ≤
        2 * (DoublingMST.mstWeight d - cutLP d Finset.univ) + θ ∧
      (cutLP d Finset.univ - (DoublingMST.mstWeight d - cutLP d Finset.univ) ≤ ∑ e ∈ E, w0 e →
        cutLP d Finset.univ - 3 * (DoublingMST.mstWeight d - cutLP d Finset.univ) - θ ≤
          ∑ e ∈ E, (if e ∈ hull E (S ∪ N) \ hull E S then 0 else w0 e)) := by
  set H := hull E (S ∪ N) \ hull E S with hH
  have hsub : hull E S ⊆ hull E (S ∪ N) := by
    intro e he
    simp only [hull, Finset.mem_filter] at he ⊢
    obtain ⟨heE, u, hu, v, hv, hp⟩ := he
    exact ⟨heE, u, Finset.mem_union_left _ hu, v, Finset.mem_union_left _ hv, hp⟩
  have hHE : H ⊆ E := by
    intro e he
    rw [hH, Finset.mem_sdiff] at he
    exact (Finset.mem_filter.mp he.1).1
  -- difference of sums
  have hdiff : ∑ e ∈ E, w0 e - ∑ e ∈ E, (if e ∈ H then 0 else w0 e) = ∑ e ∈ H, w0 e := by
    rw [← Finset.sum_sub_distrib]
    have : ∀ e ∈ E, w0 e - (if e ∈ H then 0 else w0 e) = if e ∈ H then w0 e else 0 := by
      intro e _; split_ifs <;> ring
    rw [Finset.sum_congr rfl this, ← Finset.sum_filter]
    congr 1
    ext e; simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hHE h, h⟩⟩
  have hHw : ∑ e ∈ H, w0 e ≤ DoublingMST.treeWeight d (hull E (S ∪ N)) - DoublingMST.treeWeight d (hull E S) := by
    unfold DoublingMST.treeWeight
    rw [← Finset.sum_sdiff_eq_sub hsub]
    exact Finset.sum_le_sum fun e he => (hw0.1 e (hHE he)).2
  have h44a := (lemma_4_4 d hd E hE (S ∪ N)).1
  have h44b := (lemma_4_4 d hd E hE S).2
  have hcost : ∑ e ∈ E, w0 e - ∑ e ∈ E, (if e ∈ H then 0 else w0 e) ≤
      2 * (DoublingMST.mstWeight d - cutLP d Finset.univ) + θ := by
    rw [hdiff]; linarith
  refine ⟨⟨fun e he => ?_, fun u v => ?_⟩, hcost, fun hK => by linarith⟩
  · by_cases h : e ∈ H
    · simp only [h, if_true]
      exact ⟨le_rfl, (hw0.1 e he).1.trans (hw0.1 e he).2⟩
    · simp only [h, if_false]; exact hw0.1 e he
  · refine le_trans ?_ (hw0.2 u v)
    unfold treeDist
    apply Finset.sum_le_sum
    intro e he
    have heE : e ∈ E := (Finset.mem_filter.mp he).1
    by_cases h : e ∈ H
    · simp only [h, if_true]; exact (hw0.1 e heE).1
    · simp only [h, if_false]; exact le_rfl
