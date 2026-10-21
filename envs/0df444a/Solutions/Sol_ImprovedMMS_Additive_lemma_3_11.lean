-- Prove2me | solution 1 for ImprovedMMS.Additive.lemma_3_11
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T16:47:43.27566+00:00
-- url     : https://prove2.me/submissions/02c5d1fe-08ba-4fd3-a795-aff36e6d660b

import Mathlib
import Definitions.Def_ImprovedMMS_Additive_Envy

set_option autoImplicit false
open ImprovedMMS.Additive

open Classical in
theorem solution {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ) (f g : Fin n → Finset (Fin m))
    (C : Finset (Fin n)) (hC : ∀ i ∈ C, IsSemiSatisfied f g i) (hcef : IsCycleEnvyFree v f C) :
    ∀ i : Fin n, ¬ Relation.TransGen (envyGraph v f C) i i := by
  intro i h
  set r := envyGraph v f C with hr
  let T : Finset (Fin n) := C.filter (fun x => Relation.TransGen r i x ∧ Relation.TransGen r x i)
  have hiC : i ∈ C := by
    obtain ⟨b, hb, _⟩ := Relation.TransGen.head'_iff.mp h
    exact hb.1
  have hiT : i ∈ T := by
    simp only [T, Finset.mem_filter]
    exact ⟨hiC, h, h⟩
  obtain ⟨⟨w, hw⟩, _⟩ := hcef T (Finset.filter_subset _ _) ⟨i, hiT⟩
  have hwT := hw.1
  simp only [T, Finset.mem_filter] at hwT
  obtain ⟨b, hb, hbi⟩ := Relation.TransGen.head'_iff.mp hwT.2.2
  have hbT : b ∈ T := by
    simp only [T, Finset.mem_filter]
    refine ⟨hb.2.1, hwT.2.1.tail hb, ?_⟩
    rcases Relation.reflTransGen_iff_eq_or_transGen.mp hbi with h' | h'
    · rw [← h']; exact h
    · exact h'
  exact hw.2 b hbT hb.2.2
