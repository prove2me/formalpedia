-- Prove2me | solution 1 for LatticePrepro.exists_base
-- status  : ACCEPTED   (prove)
-- author  : @WizardOfMenlo
-- created : 2026-11-13T09:27:57.752066+00:00
-- url     : https://prove2.me/submissions/8a5ad65a-70e9-4f5b-a679-8cff2d505828

import Mathlib


namespace LatticePrepro

/-- There is `B ≥ 2` with `Y ≤ B^m ≤ 2^m · Y` (the least `B ≥ 2` with `B^m ≥ Y`). -/
private lemma exists_base {Y m : ℕ} (hm : 1 ≤ m) (hY : 1 ≤ Y) :
    ∃ B : ℕ, 2 ≤ B ∧ Y ≤ B ^ m ∧ B ^ m ≤ 2 ^ m * Y := by
  classical
  have hex : ∃ B : ℕ, 2 ≤ B ∧ Y ≤ B ^ m :=
    ⟨Y + 2, by omega, le_trans (by omega) (Nat.le_self_pow (by omega) (Y + 2))⟩
  set B := Nat.find hex with hBdef
  have hP : 2 ≤ B ∧ Y ≤ B ^ m := Nat.find_spec hex
  refine ⟨B, hP.1, hP.2, ?_⟩
  rcases Nat.lt_or_ge 2 B with h2 | h2
  · -- `B ≥ 3`: minimality gives `(B - 1)^m < Y`
    have hmin : ¬ (2 ≤ B - 1 ∧ Y ≤ (B - 1) ^ m) := Nat.find_min hex (by omega)
    have hlt : (B - 1) ^ m < Y := by
      by_contra hcon
      exact hmin ⟨by omega, not_lt.mp hcon⟩
    calc B ^ m ≤ (2 * (B - 1)) ^ m := Nat.pow_le_pow_left (by omega) m
      _ = 2 ^ m * (B - 1) ^ m := by rw [mul_pow]
      _ ≤ 2 ^ m * Y := Nat.mul_le_mul_left _ hlt.le
  · have hB2 : B = 2 := le_antisymm h2 hP.1
    rw [hB2]
    exact Nat.le_mul_of_pos_right _ hY

end LatticePrepro

theorem solution {Y m : ℕ} (hm : 1 ≤ m) (hY : 1 ≤ Y) :
    ∃ B : ℕ, 2 ≤ B ∧ Y ≤ B ^ m ∧ B ^ m ≤ 2 ^ m * Y :=
  @LatticePrepro.exists_base Y m hm hY
