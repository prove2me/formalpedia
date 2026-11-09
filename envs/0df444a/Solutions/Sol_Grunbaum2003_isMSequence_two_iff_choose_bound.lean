-- Prove2me | solution 1 for Grunbaum2003.isMSequence_two_iff_choose_bound
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-09T03:42:52.956649+00:00
-- url     : https://prove2.me/submissions/929654a3-e676-447b-b141-a5448f6f42ed

import Definitions.Def_Grunbaum2003_IsMSequence
import Mathlib.Data.Nat.Find
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
open scoped BigOperators
open Grunbaum2003

private lemma icc_one_two : Finset.Icc 1 2 = {1, 2} := by decide

private lemma choose_two_succ (a : ℕ) :
    Nat.choose (a + 1) 2 = a + Nat.choose a 2 := by
  exact Nat.choose_succ_succ' a 1 |>.trans (by rw [Nat.choose_one_right])

/-- The explicit two-binomial expansion: a triangular number and a smaller remainder. -/
private lemma exists_triangular_remainder (N : ℕ) (hN : 0 < N) :
    ∃ a r : ℕ, 2 ≤ a ∧ r < a ∧ N = Nat.choose a 2 + r := by
  have hex : ∃ t : ℕ, N < Nat.choose t 2 := by
    refine ⟨N + 2, ?_⟩
    rw [show N + 2 = (N + 1) + 1 by omega, choose_two_succ]
    omega
  let t := Nat.find hex
  have ht : N < Nat.choose t 2 := Nat.find_spec hex
  have ht3 : 3 ≤ t := by
    by_contra h
    have hle : Nat.choose t 2 ≤ Nat.choose 2 2 :=
      Nat.choose_le_choose 2 (by omega)
    norm_num at hle
    omega
  let a := t - 1
  have ha : 2 ≤ a := by dsimp [a]; omega
  have hat : a < t := by dsimp [a]; omega
  have hlow : Nat.choose a 2 ≤ N := by
    exact Nat.le_of_not_gt (Nat.find_min hex hat)
  have hta : t = a + 1 := by dsimp [a]; omega
  rw [hta, choose_two_succ] at ht
  refine ⟨a, N - Nat.choose a 2, ha, ?_, ?_⟩ <;> omega

/-- In length two, the inverse Macaulay boundary is exactly the triangular upper bound. -/
theorem solution (g : ℕ → ℕ) :
    IsMSequence 2 g ↔ g 0 = 1 ∧ g 2 ≤ Nat.choose (g 1 + 1) 2 := by
  constructor
  · intro hg
    refine ⟨hg.1, ?_⟩
    rcases hg.2 2 (by omega) (by omega) with hzero | ⟨i, a, hi, hi2, hai, hstrict, hsum, hbound⟩
    · rw [hzero]
      exact Nat.zero_le _
    · have hi_cases : i = 1 ∨ i = 2 := by omega
      rcases hi_cases with rfl | rfl
      · have h12 : a 1 < a 2 := hstrict 1 2 (by omega) (by omega) (by omega)
        simp only [icc_one_two, Finset.sum_pair (by omega : (1 : ℕ) ≠ 2),
          Nat.choose_one_right, Nat.sub_self, Nat.choose_zero_right,
          show 2 - 1 = 1 from rfl] at hsum hbound
        have h2 : a 2 ≤ g 1 := by omega
        have htop := Nat.choose_le_choose 2 (Nat.add_le_add_right h2 1)
        rw [choose_two_succ] at htop
        omega
      · simp only [Finset.Icc_self, Finset.sum_singleton,
          show 2 - 1 = 1 from rfl, Nat.choose_one_right] at hsum hbound
        have h2 : a 2 ≤ g 1 + 1 := by omega
        rw [hsum]
        exact Nat.choose_le_choose 2 h2
  · rintro ⟨hg0, hmax⟩
    refine ⟨hg0, ?_⟩
    intro k hk hk2
    have hk_cases : k = 1 ∨ k = 2 := by omega
    rcases hk_cases with rfl | rfl
    · by_cases hzero : g 1 = 0
      · exact Or.inl hzero
      · refine Or.inr ⟨1, fun _ => g 1, by omega, by omega, ?_, ?_, ?_, ?_⟩
        · change 1 ≤ g 1
          omega
        · intro r s hr hrs hs
          omega
        · simp
        · simp [hg0]
    · by_cases hzero : g 2 = 0
      · exact Or.inl hzero
      · obtain ⟨a, r, ha, hr, hN⟩ := exists_triangular_remainder (g 2) (by omega)
        have ha_top : a ≤ g 1 + 1 := by
          by_contra hnot
          have hle : Nat.choose (g 1 + 2) 2 ≤ Nat.choose a 2 :=
            Nat.choose_le_choose 2 (by omega)
          rw [show g 1 + 2 = (g 1 + 1) + 1 by omega, choose_two_succ] at hle
          omega
        by_cases hr0 : r = 0
        · refine Or.inr ⟨2, fun _ => a, by omega, by omega, ha, ?_, ?_, ?_⟩
          · intro i j hi hij hj
            omega
          · simpa [hr0] using hN
          · simpa using (show a - 1 ≤ g 1 by omega)
        · have ha_small : a ≤ g 1 := by
            by_contra hn
            have heq : a = g 1 + 1 := by omega
            rw [heq] at hN
            omega
          let b : ℕ → ℕ := fun j => if j = 1 then r else a
          refine Or.inr ⟨1, b, by omega, by omega, ?_, ?_, ?_, ?_⟩
          · simp [b]
            omega
          · intro i j hi hij hj
            have hi1 : i = 1 := by omega
            have hj2 : j = 2 := by omega
            subst i
            subst j
            simpa [b] using hr
          · simpa [icc_one_two, b, Nat.add_comm] using hN
          · simp only [icc_one_two, Finset.sum_pair (by omega : (1 : ℕ) ≠ 2),
              b, if_neg (by omega : (2 : ℕ) ≠ 1), Nat.sub_self,
              Nat.choose_zero_right, show 2 - 1 = 1 from rfl, Nat.choose_one_right]
            omega
