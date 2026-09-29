-- Prove2me | solution 1 for LanglandsTunnell.casimir_pos_or_discrete_or_zero_of_weightSet
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/31d895ab-47d9-5af9-bb98-ee6e7848a7ad

import Mathlib.Data.Int.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_casimir_pos_or_discrete_or_zero_of_weightSet

set_option autoImplicit false

namespace UnitClass17

private theorem main (lam : ℝ) (S : Set ℤ) (hS : S.Nonempty)
    (hminus : ∀ n ∈ S, 0 ≤ 4 * lam + n * (n - 2))
    (hplus : ∀ n ∈ S, 0 ≤ 4 * lam + n * (n + 2))
    (clminus : ∀ n ∈ S, 0 < 4 * lam + n * (n - 2) → n - 2 ∈ S)
    (clplus : ∀ n ∈ S, 0 < 4 * lam + n * (n + 2) → n + 2 ∈ S) :
    0 < lam ∨
      (∃ k₀ : ℕ, 2 ≤ k₀ ∧ lam = ((k₀ : ℝ) / 2) * (1 - (k₀ : ℝ) / 2) ∧
        ∀ n ∈ S, (k₀ : ℤ) ≤ |n| ∧ (n - k₀) % 2 = 0) ∨
      (lam = 0 ∧ (0 : ℤ) ∈ S) := by
  classical
  by_cases hpos : 0 < lam
  · exact Or.inl hpos
  push_neg at hpos
  by_cases h0 : (0 : ℤ) ∈ S
  · refine Or.inr (Or.inr ⟨?_, h0⟩)
    have := hminus 0 h0
    push_cast at this
    linarith

  have h1 : (1 : ℤ) ∉ S := by
    intro h; have := hminus 1 h; push_cast at this; linarith
  have h1' : (-1 : ℤ) ∉ S := by
    intro h; have := hplus (-1) h; push_cast at this; linarith

  have hex : ∃ k : ℕ, ∃ n ∈ S, n.natAbs = k := by
    obtain ⟨n, hn⟩ := hS; exact ⟨n.natAbs, n, hn, rfl⟩
  set k₀ := Nat.find hex with hk₀
  obtain ⟨n₀, hn₀S, hn₀⟩ := Nat.find_spec hex
  have hmin : ∀ m ∈ S, k₀ ≤ m.natAbs := by
    intro m hm
    by_contra hlt
    push_neg at hlt
    exact Nat.find_min hex hlt ⟨m, hm, rfl⟩
  rw [← hk₀] at hn₀
  have hk2 : 2 ≤ k₀ := by
    by_contra hlt
    push_neg at hlt
    interval_cases k₀
    · have : n₀ = 0 := Int.natAbs_eq_zero.mp hn₀
      exact h0 (this ▸ hn₀S)
    · rcases Int.natAbs_eq_iff.mp hn₀ with h | h
      · exact h1 (by simpa [h] using hn₀S)
      · exact h1' (by simpa [h] using hn₀S)

  have hkey : 4 * lam + (k₀ : ℝ) * ((k₀ : ℝ) - 2) = 0 := by
    rcases Int.natAbs_eq_iff.mp hn₀ with h | h
    ·
      have hge := hminus n₀ hn₀S
      rw [h] at hge; push_cast at hge
      by_contra hne
      have hposE : 0 < 4 * lam + (n₀ : ℝ) * ((n₀ : ℝ) - 2) := by
        rw [h]; push_cast; exact lt_of_le_of_ne hge (Ne.symm hne)
      have hmem := clminus n₀ hn₀S (by exact_mod_cast hposE)
      have := hmin _ hmem
      rw [h] at this
      omega
    ·
      have hge := hplus n₀ hn₀S
      rw [h] at hge; push_cast at hge
      by_contra hne
      have hne' : 4 * lam + (-(k₀ : ℝ)) * (-(k₀ : ℝ) + 2) ≠ 0 := by
        intro h'; apply hne; linarith
      have hposE : 0 < 4 * lam + (n₀ : ℝ) * ((n₀ : ℝ) + 2) := by
        rw [h]; push_cast; exact lt_of_le_of_ne hge (Ne.symm hne')
      have hmem := clplus n₀ hn₀S (by exact_mod_cast hposE)
      have := hmin _ hmem
      rw [h] at this
      omega
  refine Or.inr (Or.inl ⟨k₀, hk2, by linarith [hkey], fun m hm => ⟨?_, ?_⟩⟩)
  · have := hmin m hm
    rw [← Int.natCast_natAbs]
    exact_mod_cast this
  ·
    have hE : ∀ m : ℤ, 4 * lam + (m : ℝ) * ((m : ℝ) - 2) = ((m * (m - 2) - (k₀ : ℤ) * ((k₀ : ℤ) - 2) : ℤ) : ℝ) := by
      intro m; push_cast; linarith [hkey]
    have hE' : ∀ m : ℤ, 4 * lam + (m : ℝ) * ((m : ℝ) + 2) = ((m * (m + 2) - (k₀ : ℤ) * ((k₀ : ℤ) - 2) : ℤ) : ℝ) := by
      intro m; push_cast; linarith [hkey]
    suffices H : ∀ d : ℕ, ∀ m ∈ S, m.natAbs = k₀ + d → (m - k₀) % 2 = 0 by
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (hmin m hm)
      exact H d m hm hd
    intro d
    induction d using Nat.strong_induction_on with
    | _ d IH =>
      intro m hm hd
      rcases Nat.lt_or_ge d 2 with hd2 | hd2
      · interval_cases d
        ·
          rcases Int.natAbs_eq_iff.mp hd with h | h <;> (rw [h]; push_cast; omega)
        ·
          exfalso
          rcases Int.natAbs_eq_iff.mp hd with h | h
          · have hp : 0 < 4 * lam + (m : ℝ) * ((m : ℝ) - 2) := by
              rw [hE]; exact_mod_cast (by rw [h]; push_cast; nlinarith : (0 : ℤ) < m * (m - 2) - k₀ * (k₀ - 2))
            have hmem := clminus m hm hp
            have := hmin _ hmem
            rw [h] at this; push_cast at this; omega
          · have hp : 0 < 4 * lam + (m : ℝ) * ((m : ℝ) + 2) := by
              rw [hE']; exact_mod_cast (by rw [h]; push_cast; nlinarith : (0 : ℤ) < m * (m + 2) - k₀ * (k₀ - 2))
            have hmem := clplus m hm hp
            have := hmin _ hmem
            rw [h] at this; push_cast at this; omega
      ·
        rcases Int.natAbs_eq_iff.mp hd with h | h
        · have hp : 0 < 4 * lam + (m : ℝ) * ((m : ℝ) - 2) := by
            rw [hE]; exact_mod_cast (by rw [h]; push_cast; nlinarith : (0 : ℤ) < m * (m - 2) - k₀ * (k₀ - 2))
          have hmem := clminus m hm hp
          have hd' : (m - 2).natAbs = k₀ + (d - 2) := by rw [h]; push_cast; omega
          have := IH (d - 2) (by omega) (m - 2) hmem hd'
          omega
        · have hp : 0 < 4 * lam + (m : ℝ) * ((m : ℝ) + 2) := by
            rw [hE']; exact_mod_cast (by rw [h]; push_cast; nlinarith : (0 : ℤ) < m * (m + 2) - k₀ * (k₀ - 2))
          have hmem := clplus m hm hp
          have hd' : (m + 2).natAbs = k₀ + (d - 2) := by rw [h]; push_cast; omega
          have := IH (d - 2) (by omega) (m + 2) hmem hd'
          omega

end UnitClass17

theorem solution
    (lam : ℝ) (S : Set ℤ) (hS : S.Nonempty)
    (hminus : ∀ n ∈ S, 0 ≤ 4 * lam + n * (n - 2))
    (hplus : ∀ n ∈ S, 0 ≤ 4 * lam + n * (n + 2))
    (clminus : ∀ n ∈ S, 0 < 4 * lam + n * (n - 2) → n - 2 ∈ S)
    (clplus : ∀ n ∈ S, 0 < 4 * lam + n * (n + 2) → n + 2 ∈ S) :
    0 < lam ∨
      (∃ k₀ : ℕ, 2 ≤ k₀ ∧ lam = ((k₀ : ℝ) / 2) * (1 - (k₀ : ℝ) / 2) ∧
        ∀ n ∈ S, (k₀ : ℤ) ≤ |n| ∧ (n - k₀) % 2 = 0) ∨
      (lam = 0 ∧ (0 : ℤ) ∈ S) :=
  UnitClass17.main lam S hS hminus hplus clminus clplus

end S_LanglandsTunnell_casimir_pos_or_discrete_or_zero_of_weightSet
end P2MW
export P2MW.S_LanglandsTunnell_casimir_pos_or_discrete_or_zero_of_weightSet (solution)
