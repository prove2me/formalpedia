-- Prove2me | solution 1 for NatSInfRangeAttained
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-26T20:53:11.019976+00:00
-- url     : https://prove2.me/submissions/3198fae4-f726-40de-9fda-bb4a862e3d74

import Mathlib.Order.Lattice.Nat

open Classical
noncomputable section

-- Full upstream proof body from Tablet/NatSInfRangeAttained.lean, with only the target wrapper/module layout adapted.
theorem solution {α : Type*} (f : α → ℕ) (hα : Nonempty α) :
    ∃ a : α, f a = sInf (Set.range f) ∧
      ∀ b : α, sInf (Set.range f) ≤ f b := by
  classical
  have hRange_nonempty : (Set.range f).Nonempty := by
    rcases hα with ⟨a₀⟩
    exact ⟨f a₀, ⟨a₀, rfl⟩⟩
  have hmem : sInf (Set.range f) ∈ Set.range f :=
    Nat.sInf_mem hRange_nonempty
  rcases hmem with ⟨a, ha⟩
  refine ⟨a, ha, ?_⟩
  intro b
  exact Nat.sInf_le ⟨b, rfl⟩
