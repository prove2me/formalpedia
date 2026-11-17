-- Prove2me | solution 1 for KnodelPrimeCordial.offset_zero_positive_pair_classification__p2m_6898b9ca_71f5_4ea4_932e_4d60ff156641_a1
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T15:10:30.725451+00:00
-- url     : https://prove2.me/submissions/9b9adae7-14e0-4211-a531-e23abc5e291a

import Mathlib
import Definitions.Def_KnodelPrimeCordial_labelF
theorem KnodelPrimeCordial.offset_zero_positive_pair_classification__p2m_6898b9ca_71f5_4ea4_932e_4d60ff156641_a1 (j : ℕ) (hj : 0 < j) :
    Nat.Coprime (KnodelPrimeCordial.labelF (2 * j))
      (KnodelPrimeCordial.labelF (2 * j - 1)) ↔
    j % 6 ∈ ({1, 2, 4} : Finset ℕ) := by
  obtain ⟨m, r, hr, rfl⟩ : ∃ m r, r < 6 ∧ j = 6 * m + r :=
    ⟨j / 6, j % 6, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod j 6).symm⟩
  have hres : (6 * m + r) % 6 = r := by omega
  rw [hres]
  interval_cases r
  · have e1 : KnodelPrimeCordial.labelF (2 * (6 * m + 0)) = 12 * m + 2 := by
      have h12 := Nat.mod_lt (2 * (6 * m + 0)) (show 0 < 12 by norm_num)
      generalize hc : (2 * (6 * m + 0)) % 12 = c at h12
      unfold KnodelPrimeCordial.labelF; rw [hc]
      interval_cases c <;> simp <;> omega
    have e2 : KnodelPrimeCordial.labelF (2 * (6 * m + 0) - 1) = 12 * m - 2 := by
      have h12 := Nat.mod_lt (2 * (6 * m + 0) - 1) (show 0 < 12 by norm_num)
      generalize hc : (2 * (6 * m + 0) - 1) % 12 = c at h12
      unfold KnodelPrimeCordial.labelF; rw [hc]
      interval_cases c <;> simp <;> omega
    rw [e1, e2]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro h
      exact absurd h (Nat.not_coprime_of_dvd_of_dvd (by norm_num : 1 < 2)
        (Nat.dvd_of_mod_eq_zero (by omega)) (Nat.dvd_of_mod_eq_zero (by omega)))
    · intro h; omega
  · have e1 : KnodelPrimeCordial.labelF (2 * (6 * m + 1)) = 12 * m + 5 := by
      have h12 := Nat.mod_lt (2 * (6 * m + 1)) (show 0 < 12 by norm_num)
      generalize hc : (2 * (6 * m + 1)) % 12 = c at h12
      unfold KnodelPrimeCordial.labelF; rw [hc]
      interval_cases c <;> simp <;> omega
    have e2 : KnodelPrimeCordial.labelF (2 * (6 * m + 1) - 1) = 12 * m + 4 := by
      have h12 := Nat.mod_lt (2 * (6 * m + 1) - 1) (show 0 < 12 by norm_num)
      generalize hc : (2 * (6 * m + 1) - 1) % 12 = c at h12
      unfold KnodelPrimeCordial.labelF; rw [hc]
      interval_cases c <;> simp <;> omega
    rw [e1, e2]
    simp only [Finset.mem_insert, Finset.mem_singleton, true_or, iff_true]
    rw [show 12 * m + 5 = 1 + (12 * m + 4) by ring, Nat.coprime_add_self_left]
    exact Nat.coprime_one_left _
  · have e1 : KnodelPrimeCordial.labelF (2 * (6 * m + 2)) = 12 * m + 3 := by
      have h12 := Nat.mod_lt (2 * (6 * m + 2)) (show 0 < 12 by norm_num)
      generalize hc : (2 * (6 * m + 2)) % 12 = c at h12
      unfold KnodelPrimeCordial.labelF; rw [hc]
      interval_cases c <;> simp <;> omega
    have e2 : KnodelPrimeCordial.labelF (2 * (6 * m + 2) - 1) = 12 * m + 1 := by
      have h12 := Nat.mod_lt (2 * (6 * m + 2) - 1) (show 0 < 12 by norm_num)
      generalize hc : (2 * (6 * m + 2) - 1) % 12 = c at h12
      unfold KnodelPrimeCordial.labelF; rw [hc]
      interval_cases c <;> simp <;> omega
    rw [e1, e2]
    simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true, iff_true]
    rw [show 12 * m + 3 = 2 + (12 * m + 1) by ring, Nat.coprime_add_self_left, Nat.coprime_two_left]
    exact ⟨6 * m, by ring⟩
  · have e1 : KnodelPrimeCordial.labelF (2 * (6 * m + 3)) = 12 * m + 8 := by
      have h12 := Nat.mod_lt (2 * (6 * m + 3)) (show 0 < 12 by norm_num)
      generalize hc : (2 * (6 * m + 3)) % 12 = c at h12
      unfold KnodelPrimeCordial.labelF; rw [hc]
      interval_cases c <;> simp <;> omega
    have e2 : KnodelPrimeCordial.labelF (2 * (6 * m + 3) - 1) = 12 * m + 6 := by
      have h12 := Nat.mod_lt (2 * (6 * m + 3) - 1) (show 0 < 12 by norm_num)
      generalize hc : (2 * (6 * m + 3) - 1) % 12 = c at h12
      unfold KnodelPrimeCordial.labelF; rw [hc]
      interval_cases c <;> simp <;> omega
    rw [e1, e2]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro h
      exact absurd h (Nat.not_coprime_of_dvd_of_dvd (by norm_num : 1 < 2)
        (Nat.dvd_of_mod_eq_zero (by omega)) (Nat.dvd_of_mod_eq_zero (by omega)))
    · intro h; omega
  · have e1 : KnodelPrimeCordial.labelF (2 * (6 * m + 4)) = 12 * m + 7 := by
      have h12 := Nat.mod_lt (2 * (6 * m + 4)) (show 0 < 12 by norm_num)
      generalize hc : (2 * (6 * m + 4)) % 12 = c at h12
      unfold KnodelPrimeCordial.labelF; rw [hc]
      interval_cases c <;> simp <;> omega
    have e2 : KnodelPrimeCordial.labelF (2 * (6 * m + 4) - 1) = 12 * m + 11 := by
      have h12 := Nat.mod_lt (2 * (6 * m + 4) - 1) (show 0 < 12 by norm_num)
      generalize hc : (2 * (6 * m + 4) - 1) % 12 = c at h12
      unfold KnodelPrimeCordial.labelF; rw [hc]
      interval_cases c <;> simp <;> omega
    rw [e1, e2]
    simp only [Finset.mem_insert, Finset.mem_singleton, or_true, iff_true]
    rw [show 12 * m + 11 = 4 + (12 * m + 7) by ring, Nat.coprime_add_self_right,
      show (4 : ℕ) = 2 ^ 2 by norm_num]
    exact Nat.Coprime.pow_right 2 (Nat.coprime_two_right.mpr ⟨6 * m + 3, by ring⟩)
  · have e1 : KnodelPrimeCordial.labelF (2 * (6 * m + 5)) = 12 * m + 12 := by
      have h12 := Nat.mod_lt (2 * (6 * m + 5)) (show 0 < 12 by norm_num)
      generalize hc : (2 * (6 * m + 5)) % 12 = c at h12
      unfold KnodelPrimeCordial.labelF; rw [hc]
      interval_cases c <;> simp <;> omega
    have e2 : KnodelPrimeCordial.labelF (2 * (6 * m + 5) - 1) = 12 * m + 9 := by
      have h12 := Nat.mod_lt (2 * (6 * m + 5) - 1) (show 0 < 12 by norm_num)
      generalize hc : (2 * (6 * m + 5) - 1) % 12 = c at h12
      unfold KnodelPrimeCordial.labelF; rw [hc]
      interval_cases c <;> simp <;> omega
    rw [e1, e2]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro h
      exact absurd h (Nat.not_coprime_of_dvd_of_dvd (by norm_num : 1 < 3)
        (Nat.dvd_of_mod_eq_zero (by omega)) (Nat.dvd_of_mod_eq_zero (by omega)))
    · intro h; omega

theorem solution (j : ℕ) (hj : 0 < j) :
    Nat.Coprime (KnodelPrimeCordial.labelF (2 * j))
      (KnodelPrimeCordial.labelF (2 * j - 1)) ↔
    j % 6 ∈ ({1, 2, 4} : Finset ℕ) := by
  obtain ⟨m, r, hr, rfl⟩ : ∃ m r, r < 6 ∧ j = 6 * m + r :=
    ⟨j / 6, j % 6, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod j 6).symm⟩
  have hres : (6 * m + r) % 6 = r := by omega
  rw [hres]
  interval_cases r
  · have e1 : KnodelPrimeCordial.labelF (2 * (6 * m + 0)) = 12 * m + 2 := by
      have h12 := Nat.mod_lt (2 * (6 * m + 0)) (show 0 < 12 by norm_num)
      generalize hc : (2 * (6 * m + 0)) % 12 = c at h12
      unfold KnodelPrimeCordial.labelF; rw [hc]
      interval_cases c <;> simp <;> omega
    have e2 : KnodelPrimeCordial.labelF (2 * (6 * m + 0) - 1) = 12 * m - 2 := by
      have h12 := Nat.mod_lt (2 * (6 * m + 0) - 1) (show 0 < 12 by norm_num)
      generalize hc : (2 * (6 * m + 0) - 1) % 12 = c at h12
      unfold KnodelPrimeCordial.labelF; rw [hc]
      interval_cases c <;> simp <;> omega
    rw [e1, e2]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro h
      exact absurd h (Nat.not_coprime_of_dvd_of_dvd (by norm_num : 1 < 2)
        (Nat.dvd_of_mod_eq_zero (by omega)) (Nat.dvd_of_mod_eq_zero (by omega)))
    · intro h; omega
  · have e1 : KnodelPrimeCordial.labelF (2 * (6 * m + 1)) = 12 * m + 5 := by
      have h12 := Nat.mod_lt (2 * (6 * m + 1)) (show 0 < 12 by norm_num)
      generalize hc : (2 * (6 * m + 1)) % 12 = c at h12
      unfold KnodelPrimeCordial.labelF; rw [hc]
      interval_cases c <;> simp <;> omega
    have e2 : KnodelPrimeCordial.labelF (2 * (6 * m + 1) - 1) = 12 * m + 4 := by
      have h12 := Nat.mod_lt (2 * (6 * m + 1) - 1) (show 0 < 12 by norm_num)
      generalize hc : (2 * (6 * m + 1) - 1) % 12 = c at h12
      unfold KnodelPrimeCordial.labelF; rw [hc]
      interval_cases c <;> simp <;> omega
    rw [e1, e2]
    simp only [Finset.mem_insert, Finset.mem_singleton, true_or, iff_true]
    rw [show 12 * m + 5 = 1 + (12 * m + 4) by ring, Nat.coprime_add_self_left]
    exact Nat.coprime_one_left _
  · have e1 : KnodelPrimeCordial.labelF (2 * (6 * m + 2)) = 12 * m + 3 := by
      have h12 := Nat.mod_lt (2 * (6 * m + 2)) (show 0 < 12 by norm_num)
      generalize hc : (2 * (6 * m + 2)) % 12 = c at h12
      unfold KnodelPrimeCordial.labelF; rw [hc]
      interval_cases c <;> simp <;> omega
    have e2 : KnodelPrimeCordial.labelF (2 * (6 * m + 2) - 1) = 12 * m + 1 := by
      have h12 := Nat.mod_lt (2 * (6 * m + 2) - 1) (show 0 < 12 by norm_num)
      generalize hc : (2 * (6 * m + 2) - 1) % 12 = c at h12
      unfold KnodelPrimeCordial.labelF; rw [hc]
      interval_cases c <;> simp <;> omega
    rw [e1, e2]
    simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true, iff_true]
    rw [show 12 * m + 3 = 2 + (12 * m + 1) by ring, Nat.coprime_add_self_left, Nat.coprime_two_left]
    exact ⟨6 * m, by ring⟩
  · have e1 : KnodelPrimeCordial.labelF (2 * (6 * m + 3)) = 12 * m + 8 := by
      have h12 := Nat.mod_lt (2 * (6 * m + 3)) (show 0 < 12 by norm_num)
      generalize hc : (2 * (6 * m + 3)) % 12 = c at h12
      unfold KnodelPrimeCordial.labelF; rw [hc]
      interval_cases c <;> simp <;> omega
    have e2 : KnodelPrimeCordial.labelF (2 * (6 * m + 3) - 1) = 12 * m + 6 := by
      have h12 := Nat.mod_lt (2 * (6 * m + 3) - 1) (show 0 < 12 by norm_num)
      generalize hc : (2 * (6 * m + 3) - 1) % 12 = c at h12
      unfold KnodelPrimeCordial.labelF; rw [hc]
      interval_cases c <;> simp <;> omega
    rw [e1, e2]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro h
      exact absurd h (Nat.not_coprime_of_dvd_of_dvd (by norm_num : 1 < 2)
        (Nat.dvd_of_mod_eq_zero (by omega)) (Nat.dvd_of_mod_eq_zero (by omega)))
    · intro h; omega
  · have e1 : KnodelPrimeCordial.labelF (2 * (6 * m + 4)) = 12 * m + 7 := by
      have h12 := Nat.mod_lt (2 * (6 * m + 4)) (show 0 < 12 by norm_num)
      generalize hc : (2 * (6 * m + 4)) % 12 = c at h12
      unfold KnodelPrimeCordial.labelF; rw [hc]
      interval_cases c <;> simp <;> omega
    have e2 : KnodelPrimeCordial.labelF (2 * (6 * m + 4) - 1) = 12 * m + 11 := by
      have h12 := Nat.mod_lt (2 * (6 * m + 4) - 1) (show 0 < 12 by norm_num)
      generalize hc : (2 * (6 * m + 4) - 1) % 12 = c at h12
      unfold KnodelPrimeCordial.labelF; rw [hc]
      interval_cases c <;> simp <;> omega
    rw [e1, e2]
    simp only [Finset.mem_insert, Finset.mem_singleton, or_true, iff_true]
    rw [show 12 * m + 11 = 4 + (12 * m + 7) by ring, Nat.coprime_add_self_right,
      show (4 : ℕ) = 2 ^ 2 by norm_num]
    exact Nat.Coprime.pow_right 2 (Nat.coprime_two_right.mpr ⟨6 * m + 3, by ring⟩)
  · have e1 : KnodelPrimeCordial.labelF (2 * (6 * m + 5)) = 12 * m + 12 := by
      have h12 := Nat.mod_lt (2 * (6 * m + 5)) (show 0 < 12 by norm_num)
      generalize hc : (2 * (6 * m + 5)) % 12 = c at h12
      unfold KnodelPrimeCordial.labelF; rw [hc]
      interval_cases c <;> simp <;> omega
    have e2 : KnodelPrimeCordial.labelF (2 * (6 * m + 5) - 1) = 12 * m + 9 := by
      have h12 := Nat.mod_lt (2 * (6 * m + 5) - 1) (show 0 < 12 by norm_num)
      generalize hc : (2 * (6 * m + 5) - 1) % 12 = c at h12
      unfold KnodelPrimeCordial.labelF; rw [hc]
      interval_cases c <;> simp <;> omega
    rw [e1, e2]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro h
      exact absurd h (Nat.not_coprime_of_dvd_of_dvd (by norm_num : 1 < 3)
        (Nat.dvd_of_mod_eq_zero (by omega)) (Nat.dvd_of_mod_eq_zero (by omega)))
    · intro h; omega

