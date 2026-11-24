-- Prove2me | solution 1 for InteriorZeroOfSignChange
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T15:40:58.713898+00:00
-- url     : https://prove2.me/submissions/c05e25c6-c70f-4682-a6f1-86579fa5dd58

module
public import Definitions.Def_PHarmonicPoly_Preamble
public import Definitions.Def_PHarmonicPoly_InteriorZeroOfSignChange

set_option autoImplicit false
@[expose] public section
public section
theorem _root_.solution (D : ℝ → ℝ) (hD : Continuous D) (a b : ℝ)
    (hab : a < b) (hsign : D a * D b < 0) : ∃ z, a < z ∧ z < b ∧ D z = 0 := by
  have ha : D a ≠ 0 := fun h => by rw [h] at hsign; simp at hsign
  have hb : D b ≠ 0 := fun h => by rw [h] at hsign; simp at hsign
  have key : ∃ z ∈ Set.Icc a b, D z = 0 := by
    rcases lt_or_gt_of_ne ha with h1 | h1
    · have h2 : 0 < D b := by
        rcases lt_or_gt_of_ne hb with h3 | h3
        · nlinarith
        · exact h3
      obtain ⟨z, hz, hz0⟩ := intermediate_value_Icc hab.le hD.continuousOn
        (Set.mem_Icc.mpr ⟨h1.le, h2.le⟩)
      exact ⟨z, hz, hz0⟩
    · have h2 : D b < 0 := by
        rcases lt_or_gt_of_ne hb with h3 | h3
        · exact h3
        · nlinarith
      obtain ⟨z, hz, hz0⟩ := intermediate_value_Icc' hab.le hD.continuousOn
        (Set.mem_Icc.mpr ⟨h2.le, h1.le⟩)
      exact ⟨z, hz, hz0⟩
  obtain ⟨z, hz, hz0⟩ := key
  refine ⟨z, ?_, ?_, hz0⟩
  · rcases lt_or_eq_of_le hz.1 with h' | h'
    · exact h'
    · exact absurd (h' ▸ hz0) ha
  · rcases lt_or_eq_of_le hz.2 with h' | h'
    · exact h'
    · exact absurd (h' ▸ hz0 : D b = 0) hb
