-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_cutoff_finite_cell_reindex
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T20:07:38.358748+00:00
-- url     : https://prove2.me/submissions/8f224408-42e8-47bb-b706-9d96e9aa529c

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch04_ito43_cutoff_finite_large_support
import Theorems.Thm_Kyprianou_Ch04_ito43_cutoff_finite_series_reindex
import Theorems.Thm_Kyprianou_Ch04_ito43_cutoff_finite_locator_geometry
import Theorems.Thm_Kyprianou_Ch04_ito43_cutoff_clipped_no_spurious
import Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_right_closed_grid_cell_locator_unique
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution (X L : NNReal → ℝ)
    (hCad : IsCadlag X)
    (hLeft : ∀ s : NNReal, 0 < s →
      Tendsto X (nhdsWithin s (Iio s)) (nhds (L s)))
    (K : NNReal → ℝ → ℝ → ℝ)
    (hK : Continuous (fun p : NNReal × ℝ × ℝ => K p.1 p.2.1 p.2.2))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hzero : ∀ s x z, |z| ≤ ρ → K s x z = 0)
    (T : NNReal) :
    let u : ℕ → ℕ → NNReal := fun n k => T * (k : NNReal) / (n : NNReal)
    let C : ℕ → NNReal → ℕ → ℝ := fun n t k =>
      K (u n k) (X (u n k))
        (X (min t (u n (k+1))) - X (min t (u n k)))
    let A : NNReal → NNReal → ℝ := fun t s =>
      if s ≤ t then K s (L s) (X s-L s) else 0
    ∃ (S : Finset NNReal) (j : NNReal → ℕ → ℕ),
      (∀ s ∈ S, 0 < s ∧ s ≤ T) ∧
      (∀ᶠ n : ℕ in atTop, ∀ s ∈ S,
        j s n < n ∧ u n (j s n) < s ∧ s ≤ u n (j s n+1)) ∧
      (∀ᶠ n : ℕ in atTop, ∀ t ≤ T,
        (∑ k ∈ Finset.range n, C n t k) = ∑ s ∈ S, C n t (j s n)) ∧
      (∀ t ≤ T, (∑' s : Ioc (0 : NNReal) t, K s.1 (L s.1) (X s.1-L s.1)) =
        ∑ s ∈ S, A t s) := by
  intro u C A
  classical
  let Q : Set NNReal := {s | 0 < s ∧ s ≤ T ∧ ρ ≤ |X s-L s|}
  have hf : Q.Finite :=
    Kyprianou.Ch04.ito43_cutoff_finite_large_support X L hCad hLeft T ρ hρ
  let S := hf.toFinset
  have hS (s : NNReal) : s ∈ S ↔ 0 < s ∧ s ≤ T ∧ ρ ≤ |X s-L s| := by
    simp [S,Q]
  obtain ⟨j,hj,hi⟩ := Kyprianou.Ch04.ito43_cutoff_finite_locator_geometry T S
    (fun s hs => ⟨((hS s).mp hs).1,((hS s).mp hs).2.1⟩)
  have hsp := Kyprianou.Ch04.ito43_cutoff_clipped_no_spurious X L hCad hLeft T ρ hρ
  refine ⟨S,j,fun s hs => ⟨((hS s).mp hs).1,((hS s).mp hs).2.1⟩,hj,?_,?_⟩
  · filter_upwards [hj,hi,hsp] with n hn hin hlarge
    intro t ht
    have hsub : S.image (fun s => j s n) ⊆ Finset.range n := by
      intro k hk
      obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hk
      exact Finset.mem_range.mpr (hn s hs).1
    rw [← Finset.sum_image hin]
    symm
    apply Finset.sum_subset hsub
    intro k hk hnot
    by_contra hz
    have hd : ρ < |X (min t (u n (k+1)))-X (min t (u n k))| := by
      by_contra h
      exact hz (hzero _ _ _ (le_of_not_gt h))
    obtain ⟨s,ha,hb,hs⟩ := hlarge t ht k (Finset.mem_range.mp hk) hd.le
    change min t (u n k) < s at ha
    change s ≤ min t (u n (k+1)) at hb
    have hs0 : 0 < s := (zero_le : (0:NNReal) ≤ min t (u n k)).trans_lt ha
    have hsT : s ≤ T := hb.trans ((min_le_left _ _).trans ht)
    have hmem := (hS s).mpr ⟨hs0,hsT,hs⟩
    have htk : u n k < t := by
      by_contra h
      rw [min_eq_left (le_of_not_gt h)] at ha
      exact (not_lt_of_ge (hb.trans (min_le_left _ _))) ha
    have hak : u n k < s := by simpa only [min_eq_right htk.le] using ha
    have hbk : s ≤ u n (k+1) := hb.trans (min_le_right _ _)
    have hu_eq (i : ℕ) : u n i = (i:NNReal)*(T/(n:NNReal)) := by
      dsimp [u]
      ring
    have hL := (hn s hmem).2.1
    have hR := (hn s hmem).2.2
    change u n (j s n) < s at hL
    change s ≤ u n (j s n+1) at hR
    rw [hu_eq] at hak hbk hL hR
    have heq : k = j s n :=
      AvramDividend.Classical.avram_p2_h_cadlag_right_closed_grid_cell_locator_unique
        (T/(n:NNReal)) s k (j s n) hak hbk hL hR
    exact hnot (Finset.mem_image.mpr ⟨s,hmem,heq.symm⟩)
  · exact Kyprianou.Ch04.ito43_cutoff_finite_series_reindex
      (fun s => K s (L s) (X s-L s)) T S
      (fun s hs => ⟨((hS s).mp hs).1,((hS s).mp hs).2.1⟩)
      (fun s hs ht hn => hzero _ _ _ (le_of_not_ge (fun h => hn ((hS s).mpr ⟨hs,ht,h⟩))))
