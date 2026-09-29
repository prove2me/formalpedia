-- Prove2me | solution 1 for MagicNumberShellModel.harmonic_oscillator_magic_numbers
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T09:40:35.697945+00:00
-- url     : https://prove2.me/submissions/a3c9d953-3da7-42e4-9530-5faf813c238f

import Definitions.Def_magic_number_shell_model

open MagicNumberShellModel

theorem M_card_oscillatorLevel (n : ℕ) :
    (oscillatorLevel n).card = (n + 2).choose 2 := by
  classical
  have hbij : (oscillatorLevel n).card =
      ((Finset.HasAntidiagonal.antidiagonal n).sigma fun p => Finset.HasAntidiagonal.antidiagonal p.2).card := by
    apply Finset.card_nbij' (fun q => ⟨(q.1, q.2.1 + q.2.2), (q.2.1, q.2.2)⟩)
      (fun r => (r.1.1, r.2.1, r.2.2))
    · rintro ⟨x, y, z⟩ h
      simp [oscillatorLevel, Finset.mem_sigma, Finset.HasAntidiagonal.mem_antidiagonal] at h ⊢
      omega
    · rintro ⟨⟨x, r⟩, ⟨y, z⟩⟩ h
      simp [oscillatorLevel, Finset.mem_sigma, Finset.HasAntidiagonal.mem_antidiagonal] at h ⊢
      omega
    · rintro ⟨x, y, z⟩ _; rfl
    · rintro ⟨⟨x, r⟩, ⟨y, z⟩⟩ h
      simp only [Finset.mem_coe, Finset.mem_sigma, Finset.HasAntidiagonal.mem_antidiagonal] at h
      obtain ⟨-, rfl⟩ := h
      rfl
  rw [hbij, Finset.card_sigma]
  simp only [Finset.Nat.card_antidiagonal]
  clear hbij
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.Nat.sum_antidiagonal_succ]
    simp only at ih ⊢
    rw [ih]
    have hp := Nat.choose_succ_succ' (n + 2) 1
    simp only [Nat.choose_one_right] at hp
    rw [show n + 1 + 2 = n + 2 + 1 by ring, hp]

theorem M_shellCapacity_values :
    shellCapacity 0 = 2 ∧ shellCapacity 1 = 6 ∧ shellCapacity 2 = 12 ∧
      shellCapacity 3 = 20 := by
  simp only [shellCapacity, M_card_oscillatorLevel]
  decide

theorem M_cumulativeCapacity_eq (N : ℕ) :
    cumulativeCapacity N = 2 * (N + 2).choose 3 := by
  induction N with
  | zero => simp [cumulativeCapacity]
  | succ N ih =>
    unfold cumulativeCapacity at ih ⊢
    rw [Finset.sum_range_succ, ih, shellCapacity, M_card_oscillatorLevel,
      show N + 1 + 2 = (N + 2) + 1 by ring, Nat.choose_succ_succ' (N + 2) 2]
    ring

theorem M_first_values :
    List.map cumulativeCapacity [1, 2, 3, 4] = [2, 8, 20, 40] := by
  simp only [List.map, M_cumulativeCapacity_eq]
  decide

theorem M_misses_28 :
    (28 ∈ magicNumbers ∧ ∀ N : ℕ, cumulativeCapacity N ≠ 28) ∧
      cumulativeCapacity 4 = 40 ∧ 40 ∉ magicNumbers := by
  refine ⟨⟨by decide, fun N => ?_⟩, ?_, by decide⟩
  · rw [M_cumulativeCapacity_eq]
    rcases Nat.lt_or_ge N 5 with h | h
    · interval_cases N <;> decide
    · have : (7 : ℕ).choose 3 ≤ (N + 2).choose 3 := Nat.choose_le_choose 3 (by omega)
      have h35 : (7 : ℕ).choose 3 = 35 := by decide
      omega
  · rw [M_cumulativeCapacity_eq]; decide

theorem M_harmonic :
    (∀ N : ℕ, cumulativeCapacity N = 2 * (N + 2).choose 3) ∧
      List.map cumulativeCapacity [1, 2, 3, 4] = [2, 8, 20, 40] ∧
      ({2, 8, 20} : Finset ℕ) ⊆ magicNumbers ∧
      (28 ∈ magicNumbers ∧ ∀ N : ℕ, cumulativeCapacity N ≠ 28) ∧
      (cumulativeCapacity 4 = 40 ∧ 40 ∉ magicNumbers) :=
  ⟨M_cumulativeCapacity_eq, M_first_values, by decide, M_misses_28.1, M_misses_28.2⟩

theorem solution :
    (∀ N : ℕ, cumulativeCapacity N = 2 * (N + 2).choose 3) ∧
      List.map cumulativeCapacity [1, 2, 3, 4] = [2, 8, 20, 40] ∧
      ({2, 8, 20} : Finset ℕ) ⊆ magicNumbers ∧
      (28 ∈ magicNumbers ∧ ∀ N : ℕ, cumulativeCapacity N ≠ 28) ∧
      (cumulativeCapacity 4 = 40 ∧ 40 ∉ magicNumbers) := by
  apply M_harmonic <;> assumption
