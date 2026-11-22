-- Prove2me | solution 1 for MasulloGRH.exists_cofinal_fg_subgroups_of_countable
-- status  : ACCEPTED   (prove)
-- author  : @sflicht
-- created : 2026-11-21T18:08:55.259492+00:00
-- url     : https://prove2.me/submissions/ac358bf3-085c-4508-aee4-0d02b58cf251

import Mathlib

set_option autoImplicit false

theorem solution (A : Type*) [CommGroup A] [Countable A] :
    ∃ S : ℕ → Subgroup A, Monotone S ∧ (∀ N, (S N).FG) ∧
      ∀ H : Subgroup A, H.FG → ∃ N, H ≤ S N := by
  classical
  obtain ⟨e, he⟩ := exists_surjective_nat A
  refine ⟨fun N => Subgroup.closure ((Finset.range (N + 1)).image e : Set A), ?_, ?_, ?_⟩
  · intro N M h
    refine Subgroup.closure_mono ?_
    intro x hx
    simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio] at hx ⊢
    obtain ⟨i, hi, rfl⟩ := hx
    exact ⟨i, by omega, rfl⟩
  · intro N
    exact ⟨_, rfl⟩
  · rintro H ⟨T, rfl⟩
    choose n hn using he
    refine ⟨T.sup n, Subgroup.closure_mono ?_⟩
    intro x hx
    simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio]
    exact ⟨n x, Nat.lt_succ_of_le (Finset.le_sup (f := n) hx), hn x⟩
