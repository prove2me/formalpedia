-- Prove2me | solution 1 for MNatOps.Monotone.box_step
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-25T23:25:20.241776+00:00
-- url     : https://prove2.me/submissions/b7704c05-4e2e-4556-92de-3c25390def93

import Mathlib
import Definitions.Def_MNatOps_Monotone_Model

namespace MNatOps.Monotone

private theorem inBox_of_between {n : ℕ} (l : Fin n → WithBot ℤ) (u : Fin n → WithTop ℤ)
    (a a' x : Fin n → ℤ) (ha : inBox l u a) (ha' : inBox l u a')
    (h : ∀ m, x m = a m ∨ x m = a' m ∨ (a m ≤ x m ∧ x m ≤ a' m) ∨ (a' m ≤ x m ∧ x m ≤ a m)) :
    inBox l u x := by
  intro m
  obtain ⟨h1, h2⟩ := ha m
  obtain ⟨h3, h4⟩ := ha' m
  rcases h m with e | e | ⟨p, q⟩ | ⟨p, q⟩
  · rw [e]; exact ⟨h1, h2⟩
  · rw [e]; exact ⟨h3, h4⟩
  · exact ⟨h1.trans (by exact_mod_cast p), (by exact_mod_cast q : ((x m : ℤ) : WithTop ℤ) ≤ a' m).trans h4⟩
  · exact ⟨h3.trans (by exact_mod_cast p), (by exact_mod_cast q : ((x m : ℤ) : WithTop ℤ) ≤ a m).trans h2⟩

end MNatOps.Monotone

open MNatOps.Monotone DiscreteConvex.MConvexFunctions DiscreteConvex.EconomicEquilibrium in
theorem solution {n : ℕ} (l : Fin n → WithBot ℤ) (u : Fin n → WithTop ℤ) (a a' : Fin n → ℤ)
    (ha : inBox l u a) (ha' : inBox l u a') (i : Fin n) (hi : a i < a' i)
    (j : Option (Fin n)) (hj : ∀ k, j = some k → a' k < a k) :
    inBox l u (a' - dir i j) ∧ inBox l u (a + dir i j) := by
  have key : ∀ m, (a' - dir i j) m = a m ∨ (a' - dir i j) m = a' m ∨ (a m ≤ (a' - dir i j) m ∧ (a' - dir i j) m ≤ a' m) ∨
      (a' m ≤ (a' - dir i j) m ∧ (a' - dir i j) m ≤ a m) := by
    intro m
    cases j with
    | none =>
      by_cases h : m = i
      · subst h; right; right; left; simp [dir, CharVec]; omega
      · right; left; simp [dir, CharVec, h]
    | some k =>
      have hk := hj k rfl
      by_cases h : m = i
      · subst h
        have : m ≠ k := by rintro rfl; omega
        right; right; left; simp [dir, CharVec, this]; omega
      · by_cases h2 : m = k
        · subst h2; right; right; right; simp [dir, CharVec, h]; omega
        · right; left; simp [dir, CharVec, h, h2]
  have key2 : ∀ m, (a + dir i j) m = a m ∨ (a + dir i j) m = a' m ∨ (a m ≤ (a + dir i j) m ∧ (a + dir i j) m ≤ a' m) ∨
      (a' m ≤ (a + dir i j) m ∧ (a + dir i j) m ≤ a m) := by
    intro m
    cases j with
    | none =>
      by_cases h : m = i
      · subst h; right; right; left; simp [dir, CharVec]; omega
      · left; simp [dir, CharVec, h]
    | some k =>
      have hk := hj k rfl
      by_cases h : m = i
      · subst h
        have : m ≠ k := by rintro rfl; omega
        right; right; left; simp [dir, CharVec, this]; omega
      · by_cases h2 : m = k
        · subst h2; right; right; right; simp [dir, CharVec, h]; omega
        · left; simp [dir, CharVec, h, h2]
  exact ⟨inBox_of_between l u a a' _ ha ha' key, inBox_of_between l u a a' _ ha ha' key2⟩
