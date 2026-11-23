-- Prove2me | solution 1 for NAMatchEst.lemma_3_3
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-23T00:33:16.014943+00:00
-- url     : https://prove2.me/submissions/9854333a-17f6-41d5-acbe-037aae67072b

import Mathlib
import Definitions.Def_TuranMatching_Clique_Setting
import Definitions.Def_NAMatchEst_AdjList
import Definitions.Def_NAMatchEst_AdjList_toGraph
import Definitions.Def_NAMatchEst_C0
import Definitions.Def_NAMatchEst_V1
import Definitions.Def_NAMatchEst_V1H
import Definitions.Def_NAMatchEst_RH
import Theorems.Thm_NAMatchEst_observation_3_2




namespace NAMatchEst.AuxL33

open SimpleGraph

theorem bdd {V : Type*} [Fintype V] (G : SimpleGraph V) :
    BddAbove {m | ∃ M : G.Subgraph, M.IsMatching ∧ M.edgeSet.ncard = m} := by
  refine ⟨Nat.card (Sym2 V), ?_⟩
  rintro m ⟨M, -, rfl⟩
  exact Set.ncard_le_card _

theorem exists_max {V : Type*} [Fintype V] (G : SimpleGraph V) :
    ∃ M : G.Subgraph, M.IsMatching ∧ M.edgeSet.ncard = TuranMatching.Clique.matchingNumber G :=
  Nat.sSup_mem (s := {m | ∃ M : G.Subgraph, M.IsMatching ∧ M.edgeSet.ncard = m}) ⟨0, ⊥, fun v hv => by simp at hv, by simp⟩ (bdd G)

end NAMatchEst.AuxL33

open NAMatchEst NAMatchEst.AuxL33 SimpleGraph in
theorem solution (n : ℕ) (α : ℝ) (k : ℕ) :
    (n : ℝ) ^ ((1 : ℝ) / 3) ≤ α → α ≤ (n : ℝ) ^ ((1 : ℝ) / 2) → α ≤ k → (k : ℝ) ≤ n → α ^ 2 < k →
    ∀ (G : AdjList n) (H : Finset (Fin n)), V1H G α k ⊆ H → H ⊆ V1 G α k →
      (TuranMatching.Clique.matchingNumber G.toGraph : ℝ) < k / (C0 * α) →
      ((V1 G α k).card : ℝ) ≤ k / 100 ∧ (RH G α k H : ℝ) < k * α / 100 := by
  classical
  intro h13 h12 hαk hkn hα2 G H hV1H hHV1 hlt
  obtain ⟨M, hM, hμ⟩ := exists_max G.toGraph
  obtain ⟨hcover, hcard, hc, -⟩ := observation_3_2 n α k h13 h12 hαk hkn G M hM hμ
  obtain ⟨hsub, hV1lt, hV1le⟩ := hc hlt
  set μ := TuranMatching.Clique.matchingNumber G.toGraph with hμdef
  refine ⟨le_of_lt (lt_of_lt_of_le hV1lt hV1le), ?_⟩
  -- basic numerics
  have hα : 0 < α := by
    by_contra h
    push Not at h
    have : (k : ℝ) / (C0 * α) ≤ 0 :=
      div_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _)
        (mul_nonpos_of_nonneg_of_nonpos (by norm_num [C0]) h)
    have : (0 : ℝ) ≤ μ := Nat.cast_nonneg _
    linarith
  have hkpos : (0 : ℝ) < k := lt_of_lt_of_le hα hαk
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hnα : (n : ℝ) ≤ α ^ 3 := by
    have : (n : ℝ) = ((n : ℝ) ^ ((1 : ℝ) / 3)) ^ (3 : ℕ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hn0]; norm_num
    rw [this]
    exact pow_le_pow_left₀ (Real.rpow_nonneg hn0 _) h13 3
  have hC0 : C0 = 2 ^ 20 := rfl
  set q : ℝ := k / α with hqdef
  have hqpos : 0 < q := div_pos hkpos hα
  have hkq : (k : ℝ) = q * α := by rw [hqdef, div_mul_cancel₀ _ hα.ne']
  have hq : q ≤ α ^ 2 := by
    rw [hqdef, div_le_iff₀ hα]; nlinarith
  set Δ := Delta k α with hΔdef
  have hΔ : (Δ : ℝ) ≤ 2 * q := by
    rw [hΔdef, Delta, hqdef, ← mul_div_assoc]
    exact Nat.floor_le (div_nonneg (by positivity) hα.le)
  set C := M.verts.toFinset with hC
  have hCcard : (C.card : ℝ) = 2 * μ := by
    rw [hC, ← Set.ncard_eq_toFinset_card' M.verts, hcard]; push_cast; ring
  have hX : (C.card : ℝ) < 2 * q / C0 := by
    rw [hCcard]
    have h' : (k : ℝ) / (C0 * α) = q / C0 := by rw [hqdef, div_div, mul_comm C0]
    rw [h'] at hlt
    rw [mul_div_assoc]; linarith
  -- U facts
  have hUdeg : ∀ u ∈ U G α k, ((G.adj u).length : ℝ) ≤ Δ := by
    intro u hu
    have : ¬ (Delta k α ≤ (G.adj u).length) := by
      simpa [U, V1] using hu
    push Not at this
    exact_mod_cast this.le
  -- step 1: per-vertex split
  have hstep1 : ∀ u, ((G.adj u).toFinset \ H).card ≤
      ((C \ H).filter (fun w => w ∈ G.adj u)).card + ((G.adj u).toFinset \ C).card := by
    intro u
    refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
    intro w hw
    simp only [Finset.mem_sdiff, List.mem_toFinset] at hw
    by_cases hwC : w ∈ C
    · exact Finset.mem_union_left _ (by simp [hwC, hw.1, hw.2])
    · exact Finset.mem_union_right _ (by simp [hwC, hw.1])
  -- step 2: double counting
  have hdc : ∑ u ∈ U G α k, ((C \ H).filter (fun w => w ∈ G.adj u)).card =
      ∑ w ∈ C \ H, ((U G α k).filter (fun u => w ∈ G.adj u)).card :=
    Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (fun u w => w ∈ G.adj u)
  have hterm2 : ∀ w ∈ C \ H,
      ((((U G α k).filter (fun u => w ∈ G.adj u)).card : ℕ) : ℝ) ≤ 512 * α ^ 2 + Δ := by
    intro w hw
    have hfsub : (U G α k).filter (fun u => w ∈ G.adj u) ⊆ (G.adj w).toFinset ∩ U G α k := by
      intro u hu
      simp only [Finset.mem_filter] at hu
      simp only [Finset.mem_inter, List.mem_toFinset]
      exact ⟨(G.symm u w).2 hu.2, hu.1⟩
    have hle : (((U G α k).filter (fun u => w ∈ G.adj u)).card : ℝ) ≤ dU G α k w := by
      exact_mod_cast Finset.card_le_card hfsub
    have hαsq : 0 ≤ 512 * α ^ 2 := by positivity
    have hΔ0 : (0 : ℝ) ≤ Δ := Nat.cast_nonneg _
    by_cases hwV : w ∈ V1 G α k
    · have hwH : w ∉ H := (Finset.mem_sdiff.1 hw).2
      have : w ∉ V1H G α k := fun h => hwH (hV1H h)
      have hd : (dU G α k w : ℝ) < 512 * α ^ 2 := by
        by_contra hcon
        push Not at hcon
        exact this (by simp [V1H, hwV, hcon])
      linarith
    · have hwU : w ∈ U G α k := by simp [U, hwV]
      have h1 : (dU G α k w : ℝ) ≤ (G.adj w).length := by
        rw [dU, ← List.toFinset_card_of_nodup (G.nodup w)]
        exact_mod_cast Finset.card_le_card Finset.inter_subset_left
      linarith [hUdeg w hwU]
  -- step 3
  have hterm3 : ∀ u ∈ U G α k, ((((G.adj u).toFinset \ C).card : ℕ) : ℝ) ≤
      if u ∈ C then (Δ : ℝ) else 0 := by
    intro u hu
    split_ifs with huC
    · have := hUdeg u hu
      rw [← List.toFinset_card_of_nodup (G.nodup u)] at this
      have h2 : (((G.adj u).toFinset \ C).card : ℝ) ≤ ((G.adj u).toFinset).card := by
        exact_mod_cast Finset.card_le_card Finset.sdiff_subset
      linarith
    · have : (G.adj u).toFinset \ C = ∅ := by
        ext w
        simp only [Finset.mem_sdiff, List.mem_toFinset, Finset.notMem_empty, iff_false,
          not_and, not_not]
        intro hw
        rcases hcover u w hw with h | h
        · exact absurd (by simpa [hC] using h) huC
        · simpa [hC] using h
      simp [this]
  have hsum3 : ∑ u ∈ U G α k, (if u ∈ C then (Δ : ℝ) else 0) ≤ C.card * Δ := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have : (((U G α k).filter (fun u => u ∈ C)).card : ℝ) ≤ C.card := by
      exact_mod_cast Finset.card_le_card (fun x hx => (Finset.mem_filter.1 hx).2)
    exact mul_le_mul_of_nonneg_right this (Nat.cast_nonneg _)
  have hsum2 : (∑ w ∈ C \ H, ((((U G α k).filter (fun u => w ∈ G.adj u)).card : ℕ) : ℝ)) ≤
      C.card * (512 * α ^ 2 + Δ) := by
    refine (Finset.sum_le_card_nsmul _ _ _ hterm2).trans ?_
    rw [nsmul_eq_mul]
    have : ((C \ H).card : ℝ) ≤ C.card := by
      exact_mod_cast Finset.card_le_card Finset.sdiff_subset
    exact mul_le_mul_of_nonneg_right this (by positivity)
  have hRH : (RH G α k H : ℝ) ≤ C.card * (512 * α ^ 2 + 2 * Δ) := by
    have e1 : (RH G α k H : ℝ) ≤ ∑ u ∈ U G α k,
        (((((C \ H).filter (fun w => w ∈ G.adj u)).card : ℕ) : ℝ) +
          ((((G.adj u).toFinset \ C).card : ℕ) : ℝ)) := by
      rw [RH, Nat.cast_sum]
      exact Finset.sum_le_sum fun u _ => by exact_mod_cast hstep1 u
    rw [Finset.sum_add_distrib] at e1
    have e2 : ∑ u ∈ U G α k, ((((C \ H).filter (fun w => w ∈ G.adj u)).card : ℕ) : ℝ) =
        ∑ w ∈ C \ H, ((((U G α k).filter (fun u => w ∈ G.adj u)).card : ℕ) : ℝ) := by
      rw [← Nat.cast_sum, ← Nat.cast_sum, hdc]
    have e3 : ∑ u ∈ U G α k, ((((G.adj u).toFinset \ C).card : ℕ) : ℝ) ≤ C.card * Δ :=
      (Finset.sum_le_sum hterm3).trans hsum3
    rw [e2] at e1
    nlinarith
  -- final numerics
  have hC0' : (0 : ℝ) < C0 := by rw [hC0]; norm_num
  have hX0 : (0 : ℝ) ≤ C.card := Nat.cast_nonneg _
  have f1 : (C.card : ℝ) * (512 * α ^ 2 + 2 * Δ) ≤ C.card * (516 * α ^ 2) := by
    apply mul_le_mul_of_nonneg_left _ hX0; nlinarith
  have f2 : (C.card : ℝ) * (516 * α ^ 2) ≤ (2 * q / C0) * (516 * α ^ 2) :=
    mul_le_mul_of_nonneg_right hX.le (by positivity)
  have f3 : (2 * q / C0) * (516 * α ^ 2) < k * α / 100 := by
    rw [hkq, hC0]
    have : 0 < q * α ^ 2 := by positivity
    nlinarith
  linarith
