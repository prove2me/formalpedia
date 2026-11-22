-- Prove2me | solution 1 for MasulloGRH.exists_countable_rpow_weight_domination
-- status  : ACCEPTED   (prove)
-- author  : @sflicht
-- created : 2026-11-21T18:01:19.679199+00:00
-- url     : https://prove2.me/submissions/36ca3549-cf32-47b4-a8c7-b362096812c9

import Mathlib

set_option autoImplicit false

namespace MasulloGRHHullAux

lemma rpow_le_add {y b x c : ℝ} (hy : 0 < y) (hb : b ≤ x) (hc : x ≤ c) :
    y ^ x ≤ y ^ b + y ^ c := by
  rcases le_or_gt 1 y with h | h
  · have := Real.rpow_le_rpow_of_exponent_le h hc
    linarith [Real.rpow_nonneg hy.le b]
  · have := Real.rpow_le_rpow_of_exponent_ge hy h.le hb
    linarith [Real.rpow_nonneg hy.le c]

lemma exists_seq (I : Set ℝ) (hI : I.OrdConnected) (hne : I.Nonempty) :
    ∃ a : ℕ → ℝ, (∀ j, a j ∈ I) ∧ ∀ x ∈ I, ∃ j l, a j ≤ x ∧ x ≤ a l := by
  let S : Set ℝ := ((Set.range ((↑) : ℚ → ℝ)) ∩ I) ∪ {x ∈ I | ∀ y ∈ I, y ≤ x} ∪
    {x ∈ I | ∀ y ∈ I, x ≤ y}
  have hS : S.Countable := by
    refine ((((Set.countable_range _).mono Set.inter_subset_left)).union ?_).union ?_
    · refine Set.Subsingleton.countable fun x hx y hy => le_antisymm (hy.2 x hx.1) (hx.2 y hy.1)
    · refine Set.Subsingleton.countable fun x hx y hy => le_antisymm (hx.2 y hy.1) (hy.2 x hx.1)
  have hkey : ∀ x ∈ I, (∃ s ∈ S, s ≤ x) ∧ ∃ s ∈ S, x ≤ s := by
    intro x hx
    constructor
    · by_cases h : ∀ y ∈ I, x ≤ y
      · exact ⟨x, Or.inr ⟨hx, h⟩, le_rfl⟩
      · push Not at h
        obtain ⟨y, hy, hyx⟩ := h
        obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hyx
        exact ⟨q, Or.inl (Or.inl ⟨⟨q, rfl⟩, hI.out hy hx ⟨hq1.le, hq2.le⟩⟩), hq2.le⟩
    · by_cases h : ∀ y ∈ I, y ≤ x
      · exact ⟨x, Or.inl (Or.inr ⟨hx, h⟩), le_rfl⟩
      · push Not at h
        obtain ⟨y, hy, hyx⟩ := h
        obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hyx
        exact ⟨q, Or.inl (Or.inl ⟨⟨q, rfl⟩, hI.out hx hy ⟨hq1.le, hq2.le⟩⟩), hq1.le⟩
  have hSne : S.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    obtain ⟨⟨s, hs, -⟩, -⟩ := hkey x hx
    exact ⟨s, hs⟩
  obtain ⟨a, ha⟩ := hS.exists_eq_range hSne
  have hSI : S ⊆ I := by
    rintro x ((⟨-, h⟩ | ⟨h, -⟩) | ⟨h, -⟩) <;> exact h
  refine ⟨a, fun j => hSI (ha ▸ Set.mem_range_self j), fun x hx => ?_⟩
  obtain ⟨⟨s, hs, hsx⟩, ⟨s', hs', hxs'⟩⟩ := hkey x hx
  rw [ha] at hs hs'
  obtain ⟨j, rfl⟩ := hs
  obtain ⟨l, rfl⟩ := hs'
  exact ⟨j, l, hsx, hxs'⟩

end MasulloGRHHullAux

open MasulloGRHHullAux in
theorem solution (I : Set ℝ) (hI : I.OrdConnected) (hne : I.Nonempty) :
    ∃ a : ℕ → ℝ, (∀ j, a j ∈ I) ∧
      ∀ x ∈ I, ∃ j l, ∀ y : ℝ, 0 < y → y ^ x ≤ y ^ a j + y ^ a l := by
  obtain ⟨a, haI, ha⟩ := exists_seq I hI hne
  refine ⟨a, haI, fun x hx => ?_⟩
  obtain ⟨j, l, h1, h2⟩ := ha x hx
  exact ⟨j, l, fun y hy => rpow_le_add hy h1 h2⟩
