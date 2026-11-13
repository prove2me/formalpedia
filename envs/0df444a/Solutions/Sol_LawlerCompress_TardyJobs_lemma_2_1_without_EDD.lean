-- Prove2me | solution 1 for LawlerCompress.TardyJobs.lemma_2_1_without_EDD
-- status  : ACCEPTED   (prove)
-- author  : @0xbf
-- created : 2026-11-12T14:36:47.818666+00:00
-- url     : https://prove2.me/submissions/34aa4cde-361d-4056-a411-5c7eab769a6f

import Definitions.Def_LawlerCompress_TardyJobs_Canonical

set_option autoImplicit false

open LawlerCompress.TardyJobs

namespace LawlerCompress.TardyJobs

lemma d_le_dmax {m : ℕ} (I : Instance m) (j : Fin I.n) : I.d j ≤ dmax I := by
  unfold dmax
  exact Finset.le_sup (by simp)

lemma selected_mono {m : ℕ} (I : Instance m) (j : Fin I.n) (t t' : ℕ)
    (htt' : t ≤ t') (htd : t' ≤ I.d j)
    (hsel : j ∈ tbar I (I.p j) t) : j ∈ tbar I (I.p j) t' := by
  classical
  have hj' : j ∈ eligible I (I.p j) t' := by
    simp [eligible, htd]
  have hsub : eligible I (I.p j) t' ⊆ eligible I (I.p j) t := by
    intro h hh
    simp only [eligible, Finset.mem_filter, Finset.mem_univ, true_and] at hh ⊢
    exact ⟨hh.1, le_trans htt' hh.2⟩
  have hrank :
      ((eligible I (I.p j) t').filter (fun h => higher I h j)) ⊆
      ((eligible I (I.p j) t).filter (fun h => higher I h j)) := by
    intro h hh
    exact Finset.mem_filter.mpr ⟨hsub (Finset.mem_filter.mp hh).1, (Finset.mem_filter.mp hh).2⟩
  have hcard := Finset.card_le_card hrank
  have hsel' := Finset.mem_filter.mp hsel
  exact Finset.mem_filter.mpr ⟨hj', lt_of_le_of_lt hcard hsel'.2⟩

lemma mem_cbar_iff {m : ℕ} (I : Instance m) (j : Fin I.n) (t : ℕ) :
    t ∈ cbar I j ↔ I.p j ≤ t ∧ t ≤ I.d j ∧ j ∈ tbar I (I.p j) t := by
  classical
  have hdmax := d_le_dmax I j
  constructor
  · intro ht
    rcases Finset.mem_filter.mp ht with ⟨hIcc, hsel⟩
    rcases Finset.mem_Icc.mp hIcc with ⟨hp, _⟩
    have he := (Finset.mem_filter.mp hsel).1
    simp [eligible] at he
    exact ⟨hp, he, hsel⟩
  · rintro ⟨hp, hd, hsel⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp, le_trans hd hdmax⟩, hsel⟩

lemma headD_mem_of_ne_nil {α : Type*} (l : List α) (fallback : α) (hne : l ≠ []) :
    l.headD fallback ∈ l := by
  cases l with
  | nil => contradiction
  | cons a l => simp [List.headD]

lemma headD_le_of_mem_pairwise (l : List ℕ) (fallback t : ℕ)
    (hpair : l.Pairwise (· ≤ ·)) (ht : t ∈ l) : l.headD fallback ≤ t := by
  cases l with
  | nil => simp at ht
  | cons a l =>
    have hmem : t = a ∨ t ∈ l := by simpa using ht
    rcases hmem with rfl | hmem
    · exact le_rfl
    · exact (List.pairwise_cons.mp hpair).1 t hmem

lemma range_pairwise_le (n : ℕ) : (List.range n).Pairwise (· ≤ ·) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.pairwise_append]
    refine ⟨ih, ?_, ?_⟩
    · simp
    · intro a ha b hb
      simp only [List.mem_singleton] at hb
      subst b
      exact le_of_lt (List.mem_range.mp ha)

end LawlerCompress.TardyJobs

theorem solution {m : ℕ} (I : Instance m) (j : Fin I.n) :
    I.p j ≤ a I j ∧ a I j ≤ I.d j + 1 ∧
    cbar I j = Finset.Icc (a I j) (I.d j) ∧
    (cbar I j = ∅ → a I j = I.d j + 1) := by
  classical
  let L : List ℕ := (List.range (dmax I + 1)).filter (fun t => t ∈ cbar I j)
  have hLmem : ∀ t, t ∈ L ↔ t ∈ cbar I j := by
    intro t
    dsimp [L]
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
    constructor
    · rintro ⟨_, ht⟩
      exact ht
    · intro ht
      rcases (mem_cbar_iff I j t).mp ht with ⟨_, htd, _⟩
      exact ⟨Nat.lt_succ_of_le (le_trans htd (d_le_dmax I j)), ht⟩
  have hpair : L.Pairwise (· ≤ ·) := by
    exact List.Pairwise.filter _ (range_pairwise_le _)
  by_cases hempty : cbar I j = ∅
  · have ha : a I j = I.d j + 1 := by
      simp [a, L, hempty]
    have hEq : cbar I j = Finset.Icc (a I j) (I.d j) := by
      rw [ha, Finset.Icc_eq_empty_of_lt (Nat.lt_succ_self (I.d j))]
      exact hempty
    refine ⟨?_, ?_, hEq, ?_⟩
    · rw [ha]
      exact le_trans (I.p_le_d j) (Nat.le_succ (I.d j))
    · rw [ha]
    · intro _
      exact ha
  · have hnonempty : (cbar I j).Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
    obtain ⟨t₀, ht₀⟩ := hnonempty
    have hLne : L ≠ [] := by
      intro hnil
      have : t₀ ∈ L := (hLmem t₀).2 ht₀
      simp [hnil] at this
    have ha_mem : a I j ∈ cbar I j := by
      unfold a
      exact (hLmem _).1 (headD_mem_of_ne_nil L (I.d j + 1) hLne)
    have ha_le : ∀ t, t ∈ cbar I j → a I j ≤ t := by
      intro t ht
      unfold a
      exact headD_le_of_mem_pairwise L (I.d j + 1) t hpair ((hLmem t).2 ht)
    have ha_data := (mem_cbar_iff I j (a I j)).1 ha_mem
    have hEq : cbar I j = Finset.Icc (a I j) (I.d j) := by
      ext t
      constructor
      · intro ht
        have hdata := (mem_cbar_iff I j t).1 ht
        exact Finset.mem_Icc.mpr ⟨ha_le t ht, hdata.2.1⟩
      · intro ht
        rcases Finset.mem_Icc.mp ht with ⟨hat, htd⟩
        have hsel := selected_mono I j (a I j) t hat htd ha_data.2.2
        exact (mem_cbar_iff I j t).2 ⟨le_trans ha_data.1 hat, htd, hsel⟩
    refine ⟨ha_data.1, le_trans ha_data.2.1 (Nat.le_succ (I.d j)), hEq, ?_⟩
    intro h
    exact (hempty h).elim
