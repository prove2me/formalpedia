-- Prove2me | solution 1 for KnapsackFacets.claim_a
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:23:20.380084+00:00
-- url     : https://prove2.me/submissions/ed442aae-e261-4f76-b492-c117c2f08146

import Definitions.Def_KnapsackFacets_Reduction

set_option autoImplicit false

open KnapsackFacets in
theorem solution (L : ℕ) :
    3 * L + 2 < ∑ i ∈ Finset.Icc 1 (2 * rOf L), shiftedFib i := by
  have hrec : ∀ i, shiftedFib (i + 4) = shiftedFib (i + 2) + shiftedFib (i + 3) := fun i => rfl
  have hmono : ∀ n, 1 ≤ n → shiftedFib n ≤ shiftedFib (n + 1) := by
    intro n hn
    rcases (show n = 1 ∨ n = 2 ∨ 3 ≤ n by omega) with h | h | h
    · subst h
      decide
    · subst h
      decide
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
      rw [show k + 3 + 1 = k + 4 by omega, hrec]
      omega
  have hdbl : ∀ k, 2 ^ k ≤ shiftedFib (2 * k + 2) := by
    intro k
    induction k with
    | zero => decide
    | succ k ih =>
      rw [show 2 * (k + 1) + 2 = 2 * k + 4 by omega, hrec, pow_succ]
      have h1 := hmono (2 * k + 2) (by omega)
      rw [show 2 * k + 2 + 1 = 2 * k + 3 by omega] at h1
      omega
  have hc := Nat.le_pow_clog (by norm_num : 1 < 2) (30 * L + 20)
  unfold rOf
  have hc2 : 2 ≤ Nat.clog 2 (30 * L + 20) := by
    by_contra h
    push_neg at h
    have : 2 ^ Nat.clog 2 (30 * L + 20) ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨k, hk⟩ : ∃ k, Nat.clog 2 (30 * L + 20) = k + 2 := ⟨_, (Nat.sub_add_cancel hc2).symm⟩
  rw [hk] at hc ⊢
  have hsum : shiftedFib (2 * k + 2) ≤ ∑ i ∈ Finset.Icc 1 (2 * (k + 2 - 1)), shiftedFib i := by
    rw [show 2 * (k + 2 - 1) = 2 * k + 2 by omega]
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩)
  have h1 := hdbl k
  have e2 : 2 ^ (k + 2) = 4 * 2 ^ k := by ring
  omega
