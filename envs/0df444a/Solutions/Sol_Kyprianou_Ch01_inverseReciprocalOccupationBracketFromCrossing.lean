-- Prove2me | solution 1 for Kyprianou.Ch01.inverseReciprocalOccupationBracketFromCrossing
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T15:30:51.823791+00:00
-- url     : https://prove2.me/submissions/b4e14404-1357-42c0-a90a-6d00351784f7

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
open Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} (X : ℝ≥0 → Ω → ℤ) (ω : Ω)
    (t a b : ℝ≥0)
    (hBefore : ∀ u : ℝ≥0, u < a →
      reciprocalOccupation X u ω ≤ (t : ℝ≥0∞))
    (hCross : (t : ℝ≥0∞) < reciprocalOccupation X b ω) :
    ∃ s : ℝ≥0, a ≤ s ∧ s ≤ b ∧
      inverseReciprocalOccupation X t ω = (s : WithTop ℝ≥0) := by
  let S : Set ℝ≥0 :=
    {s | (t : ℝ≥0∞) < reciprocalOccupation X s ω}
  have hne : S.Nonempty := ⟨b, hCross⟩
  have hLow : a ≤ sInf S := by
    apply le_csInf hne
    intro s hs
    by_contra hlt0
    have hsA : s < a := not_le.mp hlt0
    have hNot : ¬ (t : ℝ≥0∞) < reciprocalOccupation X s ω :=
      not_lt.mpr (hBefore s hsA)
    exact hNot hs
  have hHi : sInf S ≤ b :=
    csInf_le (OrderBot.bddBelow S) hCross
  refine ⟨sInf S, hLow, hHi, ?_⟩
  unfold inverseReciprocalOccupation
  split_ifs with h
  · rfl
  · exact False.elim (h ⟨b, hCross⟩)
