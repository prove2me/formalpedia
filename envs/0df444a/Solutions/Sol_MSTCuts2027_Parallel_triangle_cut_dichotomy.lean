-- Prove2me | solution 1 for MSTCuts2027.Parallel.triangle_cut_dichotomy
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-17T09:38:49.645401+00:00
-- url     : https://prove2.me/submissions/8bad541d-9e0a-4f5c-a408-cd0c19a665d4

import Definitions.Def_MSTCuts2027_Parallel_CutModel

open MSTCuts2027.Parallel

private theorem cut_value {V : Type} [Fintype V] [DecidableEq V]
    (F : Finset V → ℝ) {u v : V} {C : Finset V} (hC : IsMincut F u v C) :
    lam F u v = F C := by
  unfold lam
  apply le_antisymm
  · exact csInf_le ((Set.toFinite _).image F).bddBelow ⟨C, hC.1, rfl⟩
  · apply le_csInf (s := F '' {D : Finset V | Separates D u v}) ⟨F C, C, hC.1, rfl⟩
    rintro y ⟨D, hD, rfl⟩
    exact hC.2 D hD

private theorem mincut_exists {V : Type} [Fintype V] [DecidableEq V]
    (F : Finset V → ℝ) {u v : V} (h : u ≠ v) : ∃ C, IsMincut F u v C := by
  classical
  have hs : ({C : Finset V | Separates C u v} : Set (Finset V)).Nonempty := by
    refine ⟨{u}, Or.inl ⟨by simp, by simpa using Ne.symm h⟩⟩
  obtain ⟨C, hC, hm⟩ := Set.exists_min_image _ F (Set.toFinite _) hs
  exact ⟨C, hC, hm⟩

-- A cut of value strictly below an (u,v)-minimum cannot separate u and v.
private theorem low_cut_transfer {V : Type} [Fintype V] [DecidableEq V]
    (F : Finset V → ℝ) {u v x : V} {C D : Finset V}
    (hC : IsMincut F u v C) (hlt : F D < F C) :
    Separates D x v ↔ Separates D x u := by
  have hn : ¬ Separates D u v := by
    intro h
    exact (not_lt_of_ge (hC.2 D h)) hlt
  unfold Separates at *
  tauto

theorem solution {V : Type} [Fintype V] [DecidableEq V]
    (F : Finset V → ℝ) (hF : IsSymmetricCutFunction F)
    (u v x : V) (hxu : x ≠ u) (hxv : x ≠ v) (C : Finset V) (hC : IsMincut F u v C)
    (hside : x ∈ C ↔ u ∈ C) :
    Xor (lam F x v = lam F u v ∧ IsMincut F x v C)
      (lam F x v < lam F u v ∧ ∀ D : Finset V, IsMincut F x v D ↔ IsMincut F x u D) := by
  classical
  have hsep : Separates C x v := by
    have huv := hC.1
    unfold Separates at *
    tauto
  have hvC := cut_value F hC
  have hle : lam F x v ≤ lam F u v := by
    rw [hvC]
    exact csInf_le ((Set.toFinite _).image F).bddBelow ⟨C, hsep, rfl⟩
  by_cases heq : lam F x v = lam F u v
  · have hm : IsMincut F x v C := by
      refine ⟨hsep, fun D hD => ?_⟩
      rw [← hvC, ← heq]
      exact csInf_le ((Set.toFinite _).image F).bddBelow ⟨D, hD, rfl⟩
    exact Or.inl ⟨⟨heq, hm⟩, fun h => (ne_of_lt h.1) heq⟩
  · have hlt : lam F x v < lam F u v := lt_of_le_of_ne hle heq
    obtain ⟨E, hE⟩ := mincut_exists F hxv
    have heval := cut_value F hE
    have hElo : F E < F C := by rwa [← heval, ← hvC]
    have hEsep : Separates E x u := (low_cut_transfer F hC hElo).mp hE.1
    have hiff : ∀ D : Finset V, IsMincut F x v D ↔ IsMincut F x u D := by
      intro D
      constructor
      · intro hD
        have hDlo : F D < F C := (hD.2 E hE.1).trans_lt hElo
        refine ⟨(low_cut_transfer F hC hDlo).mp hD.1, fun B hB => ?_⟩
        by_cases hBlo : F B < F C
        · exact hD.2 B ((low_cut_transfer F hC hBlo).mpr hB)
        · exact hDlo.le.trans (le_of_not_gt hBlo)
      · intro hD
        have hDlo : F D < F C := (hD.2 E hEsep).trans_lt hElo
        refine ⟨(low_cut_transfer F hC hDlo).mpr hD.1, fun B hB => ?_⟩
        by_cases hBlo : F B < F C
        · exact hD.2 B ((low_cut_transfer F hC hBlo).mp hB)
        · exact hDlo.le.trans (le_of_not_gt hBlo)
    exact Or.inr ⟨⟨hlt, hiff⟩, fun h => (ne_of_lt hlt) h.1⟩
