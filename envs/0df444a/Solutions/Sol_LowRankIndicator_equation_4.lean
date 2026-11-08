-- Prove2me | solution 1 for LowRankIndicator.equation_4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T20:11:38.726192+00:00
-- url     : https://prove2.me/submissions/c35fc24d-71a2-488c-a157-bbfe7e7d0509

import Mathlib
import Definitions.Def_LowRankIndicator_Sets

open LowRankIndicator in
theorem solution {n k : ℕ} (g : (Fin k → ℝ) → EReal) (A : Matrix (Fin k) (Fin n) ℝ)
    (c : Fin n → ℝ) (Iplus : Set (Fin n)) :
    (∀ I : Finset (Fin n), VI g A c Iplus I ⊆ Q g A c Iplus) ∧
      Q g A c Iplus = ⋃ I : Finset (Fin n), VI g A c Iplus I := by
  classical
  have h1 : ∀ I : Finset (Fin n), VI g A c Iplus I ⊆ Q g A c Iplus := by
    intro I p hp
    obtain ⟨⟨⟨hobj, hplus⟩, hzero⟩, hbin, hI⟩ := hp
    refine ⟨hobj, hplus, hbin, fun i => ?_⟩
    by_cases hi : i ∈ I
    · rw [hI i hi]
      ring
    · have h0 : p.2.1 i = 0 := hzero i hi
      rw [h0, zero_mul]
  refine ⟨h1, Set.Subset.antisymm ?_ (Set.iUnion_subset h1)⟩
  intro p hp
  obtain ⟨hobj, hplus, hbin, hprod⟩ := hp
  refine Set.mem_iUnion.mpr ⟨Finset.univ.filter (fun i => p.2.2 i = 1),
    ⟨⟨hobj, hplus⟩, fun i hi => ?_⟩, hbin, fun i hi => ?_⟩
  · show p.2.1 i = 0
    have hz : p.2.2 i ≠ 1 := by simpa using hi
    have hz0 : p.2.2 i = 0 := (hbin i).resolve_right hz
    have h := hprod i
    rw [hz0, sub_zero, mul_one] at h
    exact h
  · simpa using hi
