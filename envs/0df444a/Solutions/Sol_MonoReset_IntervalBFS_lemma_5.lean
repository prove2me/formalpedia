-- Prove2me | solution 1 for MonoReset.IntervalBFS.lemma_5
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-27T04:48:53.116017+00:00
-- url     : https://prove2.me/submissions/78bf97e2-ad17-4228-8673-114952080154

import Definitions.Def_MonoReset_IntervalBFS_Model
import Definitions.Def_MonoReset_IntervalBFS_Algorithm
import Theorems.Thm_MonoReset_IntervalBFS_lemma_2
import Theorems.Thm_MonoReset_IntervalBFS_minimal_interval_reduction

open MonoReset.IntervalBFS

private lemma left_mem {n : ℕ} (I : Fin n × Fin n) : I.1 ∈ ivSet I := by
  simp only [ivSet, Finset.mem_filter, Finset.mem_univ, true_and]
  fin_omega

private lemma interval_singleton {n : ℕ} (a : Fin n) : ivSet (a, a) = {a} := by
  ext s
  simp only [ivSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  fin_omega

theorem solution {n k : ℕ} (δ : Fin k → Fin n → Fin n) (hδ : ∀ a, IsMonotonic (δ a))
    (τ : List (Fin k)) (X : Finset (Fin n)) :
    IsResetSeq δ X τ ↔
      ∃ I : Fin n × Fin n,
        ivSet I = Finset.univ.filter (fun s => run δ τ s ∈ X.image (run δ τ)) ∧
        ∃ J : Fin n × Fin n, dPrime δ τ (some I) = some J ∧ (ivSet J).card = 1 := by
  constructor
  · intro hr
    let S : Finset (Fin n) := Finset.univ.filter (fun s => run δ τ s ∈ X.image (run δ τ))
    have hS_img : S.image (run δ τ) = X.image (run δ τ) := by
      ext y
      simp only [S, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨s, ⟨x, hx, hxs⟩, rfl⟩
        exact ⟨x, hx, hxs⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x, ⟨x, hx, rfl⟩, rfl⟩
    have hS_reset : IsResetSeq δ S τ := by
      unfold IsResetSeq at hr ⊢
      rw [hS_img]
      exact hr
    obtain ⟨I, hI_min, s, hd⟩ := (minimal_interval_reduction δ hδ S τ).mp hS_reset
    simp only [minIntervals, Finset.mem_filter, Finset.mem_product] at hI_min
    rcases hI_min with ⟨⟨hI1, _⟩, hS_sub⟩
    have himg : (ivSet I).image (run δ τ) ⊆ ivSet (s, s) :=
      lemma_2 δ hδ τ I (s, s) hd
    rw [interval_singleton] at himg
    have hs_eq : ∀ x ∈ ivSet I, run δ τ x = s := by
      intro x hx
      exact Finset.mem_singleton.mp (himg (Finset.mem_image_of_mem _ hx))
    have hs_mem : s ∈ X.image (run δ τ) := by
      have h1 : run δ τ I.1 = s := hs_eq I.1 (left_mem I)
      rw [← h1]
      exact (Finset.mem_filter.mp hI1).2
    have hI_sub : ivSet I ⊆ S := by
      intro x hx
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hs_eq x hx]
      exact hs_mem
    refine ⟨I, Finset.Subset.antisymm hI_sub hS_sub, (s, s), hd, ?_⟩
    rw [interval_singleton, Finset.card_singleton]
  · rintro ⟨I, hI, J, hd, hJcard⟩
    have hI1 : I.1 ∈ ivSet I := left_mem I
    rw [hI] at hI1
    have hne : (X.image (run δ τ)).Nonempty :=
      ⟨run δ τ I.1, (Finset.mem_filter.mp hI1).2⟩
    have hX_sub : X ⊆ ivSet I := by
      intro x hx
      rw [hI]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_image_of_mem _ hx⟩
    have himg : X.image (run δ τ) ⊆ ivSet J :=
      (Finset.image_subset_image hX_sub).trans (lemma_2 δ hδ τ I J hd)
    have hle : (X.image (run δ τ)).card ≤ 1 :=
      (Finset.card_le_card himg).trans hJcard.le
    have hpos : 0 < (X.image (run δ τ)).card := Finset.card_pos.mpr hne
    unfold IsResetSeq
    omega
