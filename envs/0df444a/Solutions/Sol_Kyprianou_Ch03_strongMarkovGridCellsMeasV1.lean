-- Prove2me | solution 1 for Kyprianou.Ch03.strongMarkovGridCellsMeasV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T08:17:08.558188+00:00
-- url     : https://prove2.me/submissions/b03dfbf0-4cdc-41ce-8f35-c3ec477629d5

import Mathlib
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (tau : Omega → WithTop NNReal) (hTau : IsStoppingTime F tau)
    (g : ℕ → NNReal) (hg : StrictMono g) (k : Omega → ℕ)
    (hSub : ∀ j w, (tau w ≠ ⊤ ∧ k w ≤ j) ↔ tau w ≤ (g j : WithTop NNReal))
    (s : NNReal) :
    MeasurableSet[F s] {w | tau w ≠ ⊤ ∧ g (k w) = s} := by
  classical
  by_cases hs : s ∈ Set.range g
  · obtain ⟨j, rfl⟩ := hs
    cases j with
    | zero =>
      have he : {w | tau w ≠ ⊤ ∧ g (k w) = g 0} = {w | tau w ≤ (g 0 : WithTop NNReal)} := by
        ext w
        change (tau w ≠ ⊤ ∧ g (k w) = g 0) ↔ tau w ≤ (g 0 : WithTop NNReal)
        rw [hg.injective.eq_iff, ← hSub 0 w]
        simp
      rw [he]
      exact hTau _
    | succ j =>
      have he : {w | tau w ≠ ⊤ ∧ g (k w) = g (j+1)} =
          {w | tau w ≤ (g (j+1) : WithTop NNReal)} \
            {w | tau w ≤ (g j : WithTop NNReal)} := by
        ext w
        change (tau w ≠ ⊤ ∧ g (k w) = g (j+1)) ↔
          tau w ≤ (g (j+1) : WithTop NNReal) ∧ ¬ tau w ≤ (g j : WithTop NNReal)
        rw [hg.injective.eq_iff, ← hSub (j+1) w, ← hSub j w]
        constructor
        · rintro ⟨hd, hk⟩
          exact ⟨⟨hd, hk.le⟩, fun h => by omega⟩
        · rintro ⟨⟨hd, hk⟩, hn⟩
          exact ⟨hd, le_antisymm hk (by
            by_contra! h
            exact hn ⟨hd, by omega⟩)⟩
      rw [he]
      exact (hTau _).diff (F.mono (hg.monotone (Nat.le_succ j)) _ (hTau (g j)))
  · have he : {w | tau w ≠ ⊤ ∧ g (k w) = s} = ∅ := by
      ext w
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact fun h => hs ⟨k w, h.2⟩
    rw [he]
    exact @MeasurableSet.empty Omega (F s)
