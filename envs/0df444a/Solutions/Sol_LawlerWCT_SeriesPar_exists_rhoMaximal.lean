-- Prove2me | solution 1 for LawlerWCT.SeriesPar.exists_rhoMaximal
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T08:56:39.977601+00:00
-- url     : https://prove2.me/submissions/66594973-5e51-4044-b3b0-707e2f7e9e32

import Mathlib
import Definitions.Def_LawlerWCT_SeriesPar_Model



namespace LawlerWCT.SeriesPar

theorem exrho_core {ι : Type*} [DecidableEq ι] (N : Finset ι) (G : ι → ι → Prop)
    (p w : ι → ℝ)
    (M : Finset ι) (hM : IsModule G N M) :
    ∃ I : Finset ι, IsRhoMaximal G p w M I := by
  classical
  have hne : M.Nonempty := hM.1
  let S := M.powerset.filter (fun I => IsInitialSet G M I ∧ I.Nonempty)
  have hS : S.Nonempty := ⟨M, by
    simp only [S, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨subset_rfl, ⟨subset_rfl, fun j _ i hi _ => hi⟩, hne⟩⟩
  obtain ⟨I, hI, hmax⟩ := Finset.exists_max_image S (rho p w) hS
  simp only [S, Finset.mem_filter, Finset.mem_powerset] at hI
  refine ⟨I, hI.2.1, hI.2.2, fun I' h1 h2 => hmax I' ?_⟩
  simp only [S, Finset.mem_filter, Finset.mem_powerset]
  exact ⟨h1.1, h1, h2⟩

theorem prec_mem {ι : Type*} (T : SPTree ι) (i j : ι) (h : T.prec i j) :
    i ∈ T.leaves ∧ j ∈ T.leaves := by
  induction T with
  | leaf _ => exact h.elim
  | series l r ihl ihr =>
    simp only [SPTree.prec] at h
    simp only [SPTree.leaves, List.mem_append]
    rcases h with h | h | ⟨h1, h2⟩
    · have := ihl h; exact ⟨Or.inl this.1, Or.inl this.2⟩
    · have := ihr h; exact ⟨Or.inr this.1, Or.inr this.2⟩
    · exact ⟨Or.inl h1, Or.inr h2⟩
  | parallel l r ihl ihr =>
    simp only [SPTree.prec] at h
    simp only [SPTree.leaves, List.mem_append]
    rcases h with h | h
    · have := ihl h; exact ⟨Or.inl this.1, Or.inl this.2⟩
    · have := ihr h; exact ⟨Or.inr this.1, Or.inr this.2⟩

theorem sub_leaves {ι : Type*} {S T : SPTree ι} (h : S.IsSubtree T) : ∀ x ∈ S.leaves, x ∈ T.leaves := by
  induction h with
  | refl => exact fun x hx => hx
  | series_left _ ih => intro x hx; simp only [SPTree.leaves, List.mem_append]; exact Or.inl (ih x hx)
  | series_right _ ih => intro x hx; simp only [SPTree.leaves, List.mem_append]; exact Or.inr (ih x hx)
  | parallel_left _ ih => intro x hx; simp only [SPTree.leaves, List.mem_append]; exact Or.inl (ih x hx)
  | parallel_right _ ih => intro x hx; simp only [SPTree.leaves, List.mem_append]; exact Or.inr (ih x hx)

theorem leaves_ne {ι : Type*} (S : SPTree ι) : S.leaves ≠ [] := by
  induction S with
  | leaf _ => simp [SPTree.leaves]
  | series l r ihl _ => simp [SPTree.leaves, ihl]
  | parallel l r ihl _ => simp [SPTree.leaves, ihl]

theorem tree_mod {ι : Type*} {S T : SPTree ι} (h : S.IsSubtree T) (hT : T.leaves.Nodup) :
    ∀ j ∈ T.leaves, j ∉ S.leaves →
      (∀ m ∈ S.leaves, T.prec j m) ∨ (∀ m ∈ S.leaves, T.prec m j) ∨
        (∀ m ∈ S.leaves, ¬ T.prec j m ∧ ¬ T.prec m j) := by
  induction h with
  | refl => intro j hj hn; exact absurd hj hn
  | @series_left l r hsub ih =>
    intro j hj hn
    simp only [SPTree.leaves] at hT hj
    rw [List.nodup_append] at hT
    obtain ⟨hl, hr, hd⟩ := hT
    have hSl := sub_leaves hsub
    rcases List.mem_append.1 hj with hj | hj
    · rcases ih hl j hj hn with h | h | h
      · left; intro m hm; exact Or.inl (h m hm)
      · right; left; intro m hm; exact Or.inl (h m hm)
      · right; right; intro m hm
        obtain ⟨a, b⟩ := h m hm
        refine ⟨?_, ?_⟩
        · rintro (c | c | ⟨c1, c2⟩)
          · exact a c
          · have := (prec_mem _ _ _ c).1; exact hd j hj j this rfl
          · exact hd m (hSl m hm) m c2 rfl
        · rintro (c | c | ⟨c1, c2⟩)
          · exact b c
          · have := (prec_mem _ _ _ c).1; exact hd m (hSl m hm) m this rfl
          · exact hd j hj j c2 rfl
    · right; left; intro m hm
      exact Or.inr (Or.inr ⟨hSl m hm, hj⟩)
  | @series_right l r hsub ih =>
    intro j hj hn
    simp only [SPTree.leaves] at hT hj
    rw [List.nodup_append] at hT
    obtain ⟨hl, hr, hd⟩ := hT
    have hSl := sub_leaves hsub
    rcases List.mem_append.1 hj with hj | hj
    · left; intro m hm
      exact Or.inr (Or.inr ⟨hj, hSl m hm⟩)
    · rcases ih hr j hj hn with h | h | h
      · left; intro m hm; exact Or.inr (Or.inl (h m hm))
      · right; left; intro m hm; exact Or.inr (Or.inl (h m hm))
      · right; right; intro m hm
        obtain ⟨a, b⟩ := h m hm
        refine ⟨?_, ?_⟩
        · rintro (c | c | ⟨c1, c2⟩)
          · have := (prec_mem _ _ _ c).1; exact hd j this j hj rfl
          · exact a c
          · exact hd j c1 j hj rfl
        · rintro (c | c | ⟨c1, c2⟩)
          · have := (prec_mem _ _ _ c).1; exact hd m this m (hSl m hm) rfl
          · exact b c
          · exact hd m c1 m (hSl m hm) rfl
  | @parallel_left l r hsub ih =>
    intro j hj hn
    simp only [SPTree.leaves] at hT hj
    rw [List.nodup_append] at hT
    obtain ⟨hl, hr, hd⟩ := hT
    have hSl := sub_leaves hsub
    rcases List.mem_append.1 hj with hj | hj
    · rcases ih hl j hj hn with h | h | h
      · left; intro m hm; exact Or.inl (h m hm)
      · right; left; intro m hm; exact Or.inl (h m hm)
      · right; right; intro m hm
        obtain ⟨a, b⟩ := h m hm
        refine ⟨?_, ?_⟩
        · rintro (c | c)
          · exact a c
          · have := (prec_mem _ _ _ c).1; exact hd j hj j this rfl
        · rintro (c | c)
          · exact b c
          · have := (prec_mem _ _ _ c).1; exact hd m (hSl m hm) m this rfl
    · right; right; intro m hm
      refine ⟨?_, ?_⟩
      · rintro (c | c)
        · exact hd j (prec_mem _ _ _ c).1 j hj rfl
        · exact hd m (hSl m hm) m (prec_mem _ _ _ c).2 rfl
      · rintro (c | c)
        · exact hd j (prec_mem _ _ _ c).2 j hj rfl
        · exact hd m (hSl m hm) m (prec_mem _ _ _ c).1 rfl
  | @parallel_right l r hsub ih =>
    intro j hj hn
    simp only [SPTree.leaves] at hT hj
    rw [List.nodup_append] at hT
    obtain ⟨hl, hr, hd⟩ := hT
    have hSl := sub_leaves hsub
    rcases List.mem_append.1 hj with hj | hj
    · right; right; intro m hm
      refine ⟨?_, ?_⟩
      · rintro (c | c)
        · exact hd m (prec_mem _ _ _ c).2 m (hSl m hm) rfl
        · exact hd j hj j (prec_mem _ _ _ c).1 rfl
      · rintro (c | c)
        · exact hd m (prec_mem _ _ _ c).1 m (hSl m hm) rfl
        · exact hd j hj j (prec_mem _ _ _ c).2 rfl
    · rcases ih hr j hj hn with h | h | h
      · left; intro m hm; exact Or.inr (h m hm)
      · right; left; intro m hm; exact Or.inr (h m hm)
      · right; right; intro m hm
        obtain ⟨a, b⟩ := h m hm
        refine ⟨?_, ?_⟩
        · rintro (c | c)
          · have := (prec_mem _ _ _ c).1; exact hd j this j hj rfl
          · exact a c
        · rintro (c | c)
          · have := (prec_mem _ _ _ c).1; exact hd m this m (hSl m hm) rfl
          · exact b c

theorem submod_core {ι : Type*} [DecidableEq ι] (N : Finset ι) (G : ι → ι → Prop)
    (T : SPTree ι) (hT : T.leaves.Nodup) (hTN : ∀ j, j ∈ T.leaves ↔ j ∈ N)
    (hTG : ∀ i ∈ N, ∀ j ∈ N, Relation.TransGen G i j ↔ T.prec i j)
    (S : SPTree ι) (hS : S.IsSubtree T) :
    IsModule G N S.leaves.toFinset := by
  have hSl := sub_leaves hS
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil _ (leaves_ne S)
    exact ⟨a, by simpa using ha⟩
  · intro x hx; simp only [List.mem_toFinset] at hx; exact (hTN x).1 (hSl x hx)
  · have hm' : ∀ m ∈ S.leaves.toFinset, m ∈ N := by
      intro m hm; simp only [List.mem_toFinset] at hm; exact (hTN m).1 (hSl m hm)
    intro j hj hn
    simp only [List.mem_toFinset] at hn
    have hjT := (hTN j).2 hj
    have hm : ∀ m ∈ S.leaves.toFinset, m ∈ N := by
      intro m hm; simp only [List.mem_toFinset] at hm; exact (hTN m).1 (hSl m hm)
    rcases tree_mod hS hT j hjT hn with h | h | h
    · left; intro m hm
      exact (hTG j hj m (hm' m hm)).2 (h m (List.mem_toFinset.1 hm))
    · right; left; intro m hm
      exact (hTG m (hm' m hm) j hj).2 (h m (List.mem_toFinset.1 hm))
    · right; right; intro m hm
      have := h m (List.mem_toFinset.1 hm)
      exact ⟨fun c => this.1 ((hTG j hj m (hm' m hm)).1 c), fun c => this.2 ((hTG m (hm' m hm) j hj).1 c)⟩

end LawlerWCT.SeriesPar

open LawlerWCT.SeriesPar


theorem solution {ι : Type*} [DecidableEq ι] (N : Finset ι) (G : ι → ι → Prop)
    (hGN : ∀ i j, G i j → i ∈ N ∧ j ∈ N) (hacyc : ∀ j, ¬ Relation.TransGen G j j)
    (p w : ι → ℝ) (hp : ∀ j ∈ N, 0 < p j)
    (M : Finset ι) (hM : IsModule G N M) :
    ∃ I : Finset ι, IsRhoMaximal G p w M I := by
  exact exrho_core N G p w M hM
