-- Prove2me | solution 1 for MartOT.Abs.lemma_7_5
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T20:52:56.286968+00:00
-- url     : https://prove2.me/submissions/7df75edd-3de5-4417-9cb5-1936ce129422

import Mathlib
import Definitions.Def_MartOT_Var_Setting

namespace Aux_MOT_75

lemma g_cases (l ym yp y' z : ℝ) (hl : l * yp + (1 - l) * ym = y') (hy : ym < y' ∧ y' < yp)
    (h0 : 0 < l) (h1 : l < 1) :
    (z ≤ ym ∧ |z - y'| - l * |z - yp| - (1 - l) * |z - ym| = 0) ∨
    (ym ≤ z ∧ z ≤ y' ∧ |z - y'| - l * |z - yp| - (1 - l) * |z - ym| = (2 * l - 2) * (z - ym)) ∨
    (y' ≤ z ∧ z ≤ yp ∧ |z - y'| - l * |z - yp| - (1 - l) * |z - ym| = 2 * l * (z - yp)) ∨
    (yp ≤ z ∧ |z - y'| - l * |z - yp| - (1 - l) * |z - ym| = 0) := by
  obtain ⟨hy1, hy2⟩ := hy
  rcases le_total z ym with hz | hz
  · left
    refine ⟨hz, ?_⟩
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    linear_combination -hl
  rcases le_total z y' with hz' | hz'
  · right; left
    refine ⟨hz, hz', ?_⟩
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
    linear_combination -hl
  rcases le_total z yp with hz'' | hz''
  · right; right; left
    refine ⟨hz', hz'', ?_⟩
    rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
    linear_combination hl
  · right; right; right
    refine ⟨hz'', ?_⟩
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linear_combination hl

end Aux_MOT_75

open MeasureTheory Aux_MOT_75 in
theorem solution (x ym yp y' l : ℝ) (hx : ym < x ∧ x < yp) (hy : ym < y' ∧ y' < yp)
    (hl : l * yp + (1 - l) * ym = y') (A B : ℝ → ℝ)
    (hA : ∀ x' : ℝ, A x' = l * |x - yp| + (1 - l) * |x - ym| + |x' - y'|)
    (hB : ∀ x' : ℝ, B x' = l * |x' - yp| + (1 - l) * |x' - ym| + |x - y'|) :
    (y' < x → ∃ x0 ∈ Set.Ioo ym y',
      (∀ x' : ℝ, A x' - B x' = 0 ↔ x' = x0 ∨ x' = x) ∧
      (∀ x' : ℝ, x' ∉ Set.Icc x0 x → 0 < A x' - B x') ∧
      (∀ x' ∈ Set.Ioo x0 x, A x' - B x' < 0)) ∧
    (x < y' → ∃ x1 ∈ Set.Ioo y' yp,
      (∀ x' : ℝ, A x' - B x' = 0 ↔ x' = x1 ∨ x' = x) ∧
      (∀ x' : ℝ, x' ∉ Set.Icc x x1 → 0 < A x' - B x') ∧
      (∀ x' ∈ Set.Ioo x x1, A x' - B x' < 0)) ∧
    (y' = x → (∀ x' : ℝ, 0 ≤ A x' - B x') ∧ (∀ x' : ℝ, A x' - B x' = 0 ↔ x' = x)) := by
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  have h0 : 0 < l := by nlinarith
  have h1 : l < 1 := by nlinarith
  have h1l : 0 < 1 - l := by linarith
  have hAB : ∀ x', A x' - B x' =
      (|x' - y'| - l * |x' - yp| - (1 - l) * |x' - ym|) -
        (|x - y'| - l * |x - yp| - (1 - l) * |x - ym|) := by
    intro x'; rw [hA, hB]; ring
  have gc := fun z => g_cases l ym yp y' z hl ⟨hy1, hy2⟩ h0 h1
  refine ⟨fun hxy => ?_, fun hxy => ?_, fun hxy => ?_⟩
  · -- case y' < x
    have gx : |x - y'| - l * |x - yp| - (1 - l) * |x - ym| = 2 * l * (x - yp) := by
      rcases gc x with ⟨a, _⟩ | ⟨a, b, _⟩ | ⟨a, b, e⟩ | ⟨a, _⟩
      · linarith
      · linarith
      · exact e
      · linarith
    obtain ⟨x0, hx0⟩ : ∃ x0, x0 = ym + l * (yp - x) / (1 - l) := ⟨_, rfl⟩
    have e0 : (1 - l) * (x0 - ym) = l * (yp - x) := by
      rw [hx0]; field_simp; ring
    have hx0a : ym < x0 := by nlinarith [mul_pos h0 (by linarith : (0:ℝ) < yp - x)]
    have hx0b : x0 < y' := by
      nlinarith [mul_pos h0 (by linarith : (0:ℝ) < x - y'), mul_pos h0 h1l]
    -- sign facts
    have key : ∀ x', (x' < x0 → 0 < A x' - B x') ∧ (x' = x0 → A x' - B x' = 0) ∧
        (x0 < x' → x' < x → A x' - B x' < 0) ∧ (x' = x → A x' - B x' = 0) ∧
        (x < x' → 0 < A x' - B x') := by
      intro x'
      rw [hAB, gx]
      rcases gc x' with ⟨a, e⟩ | ⟨a, b, e⟩ | ⟨a, b, e⟩ | ⟨a, e⟩ <;> rw [e]
      · refine ⟨fun _ => by linarith [mul_pos h0 (by linarith : (0:ℝ) < yp - x)], fun h => by linarith, fun h _ => by linarith,
          fun h => by linarith, fun h => by linarith⟩
      · refine ⟨fun h => by linarith [mul_pos h1l (by linarith : (0:ℝ) < x0 - x')],
          fun h => by subst h; linarith, fun h _ => by
            linarith [mul_pos h1l (by linarith : (0:ℝ) < x' - x0)],
          fun h => by linarith, fun h => by linarith⟩
      · refine ⟨fun h => by linarith, fun h => by linarith,
          fun _ h => by linarith [mul_pos h0 (by linarith : (0:ℝ) < x - x')],
          fun h => by subst h; ring,
          fun h => by linarith [mul_pos h0 (by linarith : (0:ℝ) < x' - x)]⟩
      · refine ⟨fun h => by linarith, fun h => by linarith, fun _ h => by linarith,
          fun h => by linarith, fun _ => by linarith [mul_pos h0 (by linarith : (0:ℝ) < yp - x)]⟩
    refine ⟨x0, ⟨hx0a, hx0b⟩, fun x' => ?_, fun x' hx' => ?_, fun x' hx' => ?_⟩
    · obtain ⟨k1, k2, k3, k4, k5⟩ := key x'
      constructor
      · intro hz
        rcases lt_trichotomy x' x0 with h | h | h
        · linarith [k1 h]
        · left; exact h
        · rcases lt_trichotomy x' x with h' | h' | h'
          · linarith [k3 h h']
          · right; exact h'
          · linarith [k5 h']
      · rintro (h | h)
        · exact k2 h
        · exact k4 h
    · obtain ⟨k1, -, -, -, k5⟩ := key x'
      simp only [Set.mem_Icc, not_and_or, not_le] at hx'
      rcases hx' with h | h
      · exact k1 h
      · exact k5 h
    · exact (key x').2.2.1 hx'.1 hx'.2
  · -- case x < y'
    have gx : |x - y'| - l * |x - yp| - (1 - l) * |x - ym| = (2 * l - 2) * (x - ym) := by
      rcases gc x with ⟨a, _⟩ | ⟨a, b, e⟩ | ⟨a, b, _⟩ | ⟨a, _⟩
      · linarith
      · exact e
      · linarith
      · linarith
    obtain ⟨x1, hx1d⟩ : ∃ x1, x1 = yp - (1 - l) * (x - ym) / l := ⟨_, rfl⟩
    have e1 : l * (yp - x1) = (1 - l) * (x - ym) := by
      rw [hx1d]; field_simp; ring
    have hx1a : y' < x1 := by
      nlinarith [mul_pos h1l (by linarith : (0:ℝ) < y' - x), mul_pos h0 h1l]
    have hx1b : x1 < yp := by nlinarith [mul_pos h1l (by linarith : (0:ℝ) < x - ym)]
    have key : ∀ x', (x' < x → 0 < A x' - B x') ∧ (x' = x → A x' - B x' = 0) ∧
        (x < x' → x' < x1 → A x' - B x' < 0) ∧ (x' = x1 → A x' - B x' = 0) ∧
        (x1 < x' → 0 < A x' - B x') := by
      intro x'
      rw [hAB, gx]
      rcases gc x' with ⟨a, e⟩ | ⟨a, b, e⟩ | ⟨a, b, e⟩ | ⟨a, e⟩ <;> rw [e]
      · refine ⟨fun _ => by linarith [mul_pos h1l (by linarith : (0:ℝ) < x - ym)],
          fun h => by linarith, fun h _ => by linarith,
          fun h => by linarith, fun h => by linarith⟩
      · refine ⟨fun h => by linarith [mul_pos h1l (by linarith : (0:ℝ) < x - x')],
          fun h => by subst h; ring, fun h _ => by
            linarith [mul_pos h1l (by linarith : (0:ℝ) < x' - x)],
          fun h => by linarith, fun h => by linarith⟩
      · refine ⟨fun h => by linarith, fun h => by linarith,
          fun _ h => by linarith [mul_pos h0 (by linarith : (0:ℝ) < x1 - x')],
          fun h => by subst h; linarith,
          fun h => by linarith [mul_pos h0 (by linarith : (0:ℝ) < x' - x1)]⟩
      · refine ⟨fun h => by linarith, fun h => by linarith, fun _ h => by linarith,
          fun h => by linarith,
          fun _ => by linarith [mul_pos h1l (by linarith : (0:ℝ) < x - ym)]⟩
    refine ⟨x1, ⟨hx1a, hx1b⟩, fun x' => ?_, fun x' hx' => ?_, fun x' hx' => ?_⟩
    · obtain ⟨k1, k2, k3, k4, k5⟩ := key x'
      constructor
      · intro hz
        rcases lt_trichotomy x' x with h | h | h
        · linarith [k1 h]
        · right; exact h
        · rcases lt_trichotomy x' x1 with h' | h' | h'
          · linarith [k3 h h']
          · left; exact h'
          · linarith [k5 h']
      · rintro (h | h)
        · exact k4 h
        · exact k2 h
    · obtain ⟨k1, -, -, -, k5⟩ := key x'
      simp only [Set.mem_Icc, not_and_or, not_le] at hx'
      rcases hx' with h | h
      · exact k1 h
      · exact k5 h
    · exact (key x').2.2.1 hx'.1 hx'.2
  · -- case y' = x
    subst hxy
    have gx : |y' - y'| - l * |y' - yp| - (1 - l) * |y' - ym| = 2 * l * (y' - yp) := by
      rcases gc y' with ⟨a, _⟩ | ⟨a, b, _⟩ | ⟨a, b, e⟩ | ⟨a, _⟩
      · linarith
      · linarith
      · exact e
      · linarith
    have key : ∀ x', (x' ≠ y' → 0 < A x' - B x') ∧ (x' = y' → A x' - B x' = 0) := by
      intro x'
      rw [hAB, gx]
      rcases gc x' with ⟨a, e⟩ | ⟨a, b, e⟩ | ⟨a, b, e⟩ | ⟨a, e⟩ <;> rw [e]
      · exact ⟨fun _ => by linarith [mul_pos h0 (by linarith : (0:ℝ) < yp - y')],
          fun h => by linarith⟩
      · refine ⟨fun h => ?_, fun h => by subst h; linarith⟩
        have : x' < y' := lt_of_le_of_ne b h
        linarith [mul_pos h1l (by linarith : (0:ℝ) < y' - x')]
      · refine ⟨fun h => ?_, fun h => by subst h; ring⟩
        have : y' < x' := lt_of_le_of_ne a (Ne.symm h)
        linarith [mul_pos h0 (by linarith : (0:ℝ) < x' - y')]
      · exact ⟨fun _ => by linarith [mul_pos h0 (by linarith : (0:ℝ) < yp - y')],
          fun h => by linarith⟩
    refine ⟨fun x' => ?_, fun x' => ⟨fun hz => ?_, fun h => (key x').2 h⟩⟩
    · by_cases h : x' = y'
      · exact le_of_eq ((key x').2 h).symm
      · exact le_of_lt ((key x').1 h)
    · by_contra h
      linarith [(key x').1 h]
