-- Prove2me | solution 1 for ManneJobShop.Formulation.relaxation_admits_overlap
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T09:13:47.832296+00:00
-- url     : https://prove2.me/submissions/4e160369-2069-40c2-974f-0471a35eb49d

import Mathlib



namespace ManneJobShop.Formulation

theorem ro_core (T aj ak x : ℝ) (haj : 0 < aj) (hak : 0 < ak)
    (hajT : aj ≤ T) (hakT : ak ≤ T) :
    (∃ y : ℝ, (0 ≤ y ∧ y ≤ 1) ∧
        (T + ak) * y + (x - x) ≥ ak ∧ (T + aj) * (1 - y) + (x - x) ≥ aj) ∧
      ¬ (x - x ≥ ak ∨ x - x ≥ aj) := by
  have hT : 0 < T := lt_of_lt_of_le haj hajT
  have hpos : 0 < T + ak := by linarith
  refine ⟨⟨ak / (T + ak), ⟨by positivity, ?_⟩, ?_, ?_⟩, ?_⟩
  · rw [div_le_one hpos]; linarith
  · rw [sub_self, add_zero, mul_div_cancel₀ _ hpos.ne']
  · have : 1 - ak / (T + ak) = T / (T + ak) := by field_simp; ring
    rw [this, sub_self, add_zero, ge_iff_le, ← sub_nonneg]
    have : (T + aj) * (T / (T + ak)) - aj = (T*T - aj*ak) / (T + ak) := by field_simp; ring
    rw [this]; apply div_nonneg _ hpos.le
    nlinarith
  · rw [sub_self]; push_neg; exact ⟨hak, haj⟩

end ManneJobShop.Formulation

open ManneJobShop.Formulation


theorem solution (T aj ak x : ℝ) (haj : 0 < aj) (hak : 0 < ak)
    (hajT : aj ≤ T) (hakT : ak ≤ T) :
    (∃ y : ℝ, (0 ≤ y ∧ y ≤ 1) ∧
        (T + ak) * y + (x - x) ≥ ak ∧ (T + aj) * (1 - y) + (x - x) ≥ aj) ∧
      ¬ (x - x ≥ ak ∨ x - x ≥ aj) := by
  exact ro_core T aj ak x haj hak hajT hakT
