-- Prove2me | solution 1 for MinimalAccess.eq_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T00:26:18.196189+00:00
-- url     : https://prove2.me/submissions/906fc569-71b5-4bbc-9308-12fcb03d788d

import Mathlib
import Definitions.Def_MinimalAccess_Model
import Definitions.Def_MinimalAccess_AdjustedPriorities

open GaleShapley1962.Admissions

open MinimalAccess in
theorem solution {n m : ℕ} (P : Fin n → Pref m) (pri : Fin m → Prio n) (r : Fin n → Finset (Fin m))
    (μ : Assignment n m) (i j : Fin n) (s : Fin m) (hmax : MaxEnvyAt P pri r μ i j s)
    (hmin : ¬ MinEnvyAt P pri r μ i j s) :
    μ j = some s ∧ P i (some s) < P i (μ i) ∧ s ∈ r i ∧ s ∉ r j ∧ pri s j < pri s i ∧
      (∃ s' ∈ r i, P i (μ i) ≤ P i (some s')) ∧ 1 < (r i).card := by
  obtain ⟨hμj, hlt, hc⟩ := hmax
  have hij : i ≠ j := by
    rintro rfl
    rw [hμj] at hlt
    exact lt_irrefl _ hlt
  rcases hc with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
  · exact absurd ⟨hμj, hlt, Or.inl ⟨h1, h2, h3⟩⟩ hmin
  · exact absurd ⟨hμj, hlt, Or.inr (Or.inl ⟨h1, h2, h3⟩)⟩ hmin
  · have hne : pri s i ≠ pri s j := fun h => hij ((pri s).injective h)
    have hji : pri s j < pri s i := by
      rcases lt_or_gt_of_ne hne with h | h
      · exact absurd ⟨hμj, hlt, Or.inr (Or.inr (Or.inl ⟨h1, h2, h⟩))⟩ hmin
      · exact h
    have hex : ∃ s' ∈ r i, P i (μ i) ≤ P i (some s') := by
      by_contra hno
      exact hmin ⟨hμj, hlt, Or.inr (Or.inr (Or.inr ⟨h1, h2, hji, hno⟩))⟩
    obtain ⟨s', hs', hle⟩ := hex
    have hss : s' ≠ s := by
      rintro rfl
      exact lt_irrefl _ (lt_of_le_of_lt hle hlt)
    exact ⟨hμj, hlt, h1, h2, hji, ⟨s', hs', hle⟩,
      Finset.one_lt_card.mpr ⟨s, h1, s', hs', hss.symm⟩⟩
