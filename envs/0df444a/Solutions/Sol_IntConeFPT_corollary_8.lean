-- Prove2me | solution 1 for IntConeFPT.corollary_8
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:28:46.352385+00:00
-- url     : https://prove2.me/submissions/8db31a2f-ae57-4679-b447-3b3dce166737

import Mathlib

theorem solution (d τ : ℕ) (hd : 1 ≤ d) :
    ((Finset.univ : Finset (Fin τ → Finset (Fin d → Fin (2 ^ d)))).filter
      (fun R => ∀ t, (R t).card ≤ 2 ^ d)).card ≤ 2 ^ (τ * (d + 1 + d ^ 2 * 2 ^ d)) := by
  have hN : Fintype.card (Fin d → Fin (2 ^ d)) = 2 ^ (d * d) := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, ← pow_mul]
  have hN1 : 1 ≤ Fintype.card (Fin d → Fin (2 ^ d)) := by rw [hN]; exact Nat.one_le_two_pow
  have hS : ((Finset.univ : Finset (Finset (Fin d → Fin (2 ^ d)))).filter
      (fun S => S.card ≤ 2 ^ d)).card ≤
      (2 ^ d + 1) * (Fintype.card (Fin d → Fin (2 ^ d))) ^ (2 ^ d) := by
    calc ((Finset.univ : Finset (Finset (Fin d → Fin (2 ^ d)))).filter
          (fun S => S.card ≤ 2 ^ d)).card
        ≤ ((Finset.range (2 ^ d + 1)).biUnion
            (fun j => Finset.powersetCard j (Finset.univ : Finset (Fin d → Fin (2 ^ d))))).card := by
          apply Finset.card_le_card
          intro S hS
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
          simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_powersetCard]
          exact ⟨S.card, Nat.lt_succ_of_le hS, Finset.subset_univ _, rfl⟩
      _ ≤ ∑ j ∈ Finset.range (2 ^ d + 1),
            (Finset.powersetCard j (Finset.univ : Finset (Fin d → Fin (2 ^ d)))).card :=
          Finset.card_biUnion_le
      _ = ∑ j ∈ Finset.range (2 ^ d + 1), (Fintype.card (Fin d → Fin (2 ^ d))).choose j := by
          simp only [Finset.card_powersetCard, Finset.card_univ]
      _ ≤ ∑ _j ∈ Finset.range (2 ^ d + 1), (Fintype.card (Fin d → Fin (2 ^ d))) ^ (2 ^ d) := by
          apply Finset.sum_le_sum
          intro j hj
          exact le_trans (Nat.choose_le_pow _ j)
            (Nat.pow_le_pow_right hN1 (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)))
      _ = (2 ^ d + 1) * (Fintype.card (Fin d → Fin (2 ^ d))) ^ (2 ^ d) := by simp
  have hset : ((Finset.univ : Finset (Fin τ → Finset (Fin d → Fin (2 ^ d)))).filter
      (fun R => ∀ t, (R t).card ≤ 2 ^ d)) =
      Fintype.piFinset (fun _ : Fin τ => (Finset.univ : Finset (Finset (Fin d → Fin (2 ^ d)))).filter
        (fun S => S.card ≤ 2 ^ d)) := by
    ext R
    simp [Fintype.mem_piFinset]
  rw [hset, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hK1 : 2 ^ d + 1 ≤ 2 ^ (d + 1) := by
    rw [pow_succ]
    have := Nat.one_le_two_pow (n := d)
    omega
  have hNK : (Fintype.card (Fin d → Fin (2 ^ d))) ^ (2 ^ d) = 2 ^ (d ^ 2 * 2 ^ d) := by
    rw [hN, ← pow_mul, sq]
  calc (((Finset.univ : Finset (Finset (Fin d → Fin (2 ^ d)))).filter
          (fun S => S.card ≤ 2 ^ d)).card) ^ τ
      ≤ ((2 ^ d + 1) * (Fintype.card (Fin d → Fin (2 ^ d))) ^ (2 ^ d)) ^ τ :=
        Nat.pow_le_pow_left hS τ
    _ ≤ (2 ^ (d + 1) * 2 ^ (d ^ 2 * 2 ^ d)) ^ τ := by
        rw [hNK]
        exact Nat.pow_le_pow_left (Nat.mul_le_mul_right _ hK1) τ
    _ = 2 ^ (τ * (d + 1 + d ^ 2 * 2 ^ d)) := by
        rw [← pow_add, ← pow_mul, mul_comm]
