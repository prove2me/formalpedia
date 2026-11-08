-- Prove2me | solution 1 for MaxEntSampling.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T19:18:57.941472+00:00
-- url     : https://prove2.me/submissions/3c4a132f-7baf-4c05-ae5a-1d2e3d9b8c89

import Mathlib
import Definitions.Def_MaxEntSampling_IsKIndex

namespace Aux_MESl2

open Finset

noncomputable def T {d : ℕ} (lam : Fin d → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ univ.filter (fun i : Fin d => k ≤ i.val), lam i

theorem T_succ {d : ℕ} (lam : Fin d → ℝ) (k : ℕ) (hk : k < d) :
    T lam k = lam ⟨k, hk⟩ + T lam (k + 1) := by
  unfold T
  rw [Finset.sum_filter, Finset.sum_filter,
    show lam ⟨k, hk⟩ = ∑ i : Fin d, (if i = ⟨k, hk⟩ then lam i else 0) by simp,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h1 : i = ⟨k, hk⟩
  · subst h1; simp
  · have : i.val ≠ k := fun h => h1 (Fin.ext h)
    rw [if_neg h1]
    by_cases h2 : k ≤ i.val
    · rw [if_pos h2, if_pos (by omega)]; ring
    · rw [if_neg h2, if_neg (by omega)]; ring

theorem T_nonneg {d : ℕ} (lam : Fin d → ℝ) (hnn : ∀ i, 0 ≤ lam i) (k : ℕ) : 0 ≤ T lam k :=
  Finset.sum_nonneg (fun i _ => hnn i)

def P {d : ℕ} (s : ℕ) (lam : Fin d → ℝ) (k : ℕ) : Prop :=
  ∀ j : Fin d, j.val = k → lam j ≤ T lam k / ((s : ℝ) - k)

theorem P_iff {d : ℕ} (s : ℕ) (hsd : s ≤ d) (lam : Fin d → ℝ) (k : ℕ) (hk : k < s) :
    P s lam k ↔ ((s : ℝ) - k) * lam ⟨k, by omega⟩ ≤ T lam k := by
  have hpos : (0 : ℝ) < (s : ℝ) - k := by
    have : (k : ℝ) < s := by exact_mod_cast hk
    linarith
  unfold P
  constructor
  · intro h
    have := h ⟨k, by omega⟩ rfl
    rw [le_div_iff₀ hpos] at this
    linarith
  · intro h j hj
    have : j = ⟨k, by omega⟩ := Fin.ext hj
    rw [this, le_div_iff₀ hpos]
    linarith

end Aux_MESl2

open MaxEntSampling Aux_MESl2 in
theorem solution {d : ℕ} (s : ℕ) (hs1 : 1 ≤ s) (hsd : s ≤ d) (lam : Fin d → ℝ)
    (hanti : Antitone lam) (hnn : ∀ i, 0 ≤ lam i) :
    ∃! k : ℕ, IsKIndex s lam k := by
  -- R(k) ↔ ¬ P(k-1)
  have key : ∀ k, 1 ≤ k → k < s →
      ((∀ j : Fin d, j.val + 1 = k → T lam k / ((s : ℝ) - k) < lam j) ↔ ¬ P s lam (k - 1)) := by
    intro k hk1 hks
    have hpos : (0 : ℝ) < (s : ℝ) - k := by
      have : (k : ℝ) < s := by exact_mod_cast hks
      linarith
    rw [P_iff s hsd lam (k - 1) (by omega)]
    have hT := T_succ lam (k - 1) (by omega)
    rw [show k - 1 + 1 = k by omega] at hT
    have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
      rw [Nat.cast_sub hk1]; simp
    rw [hcast, hT]
    constructor
    · intro h hc
      have := h ⟨k - 1, by omega⟩ (by show k - 1 + 1 = k; omega)
      rw [div_lt_iff₀ hpos] at this
      nlinarith
    · intro h j hj
      have : j = ⟨k - 1, by omega⟩ := Fin.ext (by show j.val = k - 1; omega)
      rw [this, div_lt_iff₀ hpos]
      push_neg at h
      nlinarith
  have mono : ∀ k, k + 1 < s → P s lam k → P s lam (k + 1) := by
    intro k hk hP
    rw [P_iff s hsd lam k (by omega)] at hP
    rw [P_iff s hsd lam (k + 1) hk]
    have hT := T_succ lam k (by omega)
    have hle : lam ⟨k + 1, by omega⟩ ≤ lam ⟨k, by omega⟩ := hanti (Fin.mk_le_mk.mpr (by omega))
    have hpos : (0 : ℝ) ≤ (s : ℝ) - (k + 1 : ℕ) := by
      have : ((k + 1 : ℕ) : ℝ) < s := by exact_mod_cast hk
      linarith
    push_cast at hpos ⊢
    nlinarith
  have mono' : ∀ k0, P s lam k0 → ∀ k, k0 ≤ k → k < s → P s lam k := by
    intro k0 h0 k hk hks
    induction k, hk using Nat.le_induction with
    | base => exact h0
    | succ k hk ih => exact mono k hks (ih (by omega))
  have hlast : P s lam (s - 1) := by
    rw [P_iff s hsd lam (s - 1) (by omega)]
    have hT := T_succ lam (s - 1) (by omega)
    have hcast : ((s - 1 : ℕ) : ℝ) = (s : ℝ) - 1 := by rw [Nat.cast_sub hs1]; simp
    rw [hcast, hT]
    have := T_nonneg lam hnn (s - 1 + 1)
    linarith
  have hex : ∃ k, k < s ∧ P s lam k := ⟨s - 1, by omega, hlast⟩
  classical
  refine ⟨Nat.find hex, ?_, ?_⟩
  · obtain ⟨hk, hP⟩ := Nat.find_spec hex
    refine ⟨hk, ?_, hP⟩
    by_cases h0 : Nat.find hex = 0
    · intro j hj; omega
    · refine (key _ (by omega) hk).mpr ?_
      intro hP'
      exact Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega) ⟨by omega, hP'⟩
  · intro k ⟨hk, hR, hP⟩
    obtain ⟨hk0, hP0⟩ := Nat.find_spec hex
    rcases lt_trichotomy k (Nat.find hex) with h | h | h
    · exact absurd ⟨hk, hP⟩ (Nat.find_min hex h)
    · exact h
    · exfalso
      have hR' := (key k (by omega) hk).mp hR
      exact hR' (mono' _ hP0 (k - 1) (by omega) (by omega))
