-- Prove2me | solution 1 for IPProximity.Eisenbrand.partial_sum_pigeonhole
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-27T22:13:16.912979+00:00
-- url     : https://prove2.me/submissions/59636d00-0a2f-4a93-8bf2-23db6e1698a6

import Mathlib

theorem solution {m L : ℕ} (Δ : ℕ) (p : Fin L → Fin m → ℤ)
    (hp : ∀ k i, |p k i| ≤ (m : ℤ) * Δ)
    (hmult : ∀ v : Fin m → ℤ, (Finset.univ.filter (fun k : Fin L => p k = v)).card ≤ m) :
    L ≤ m * (2 * m * Δ + 1) ^ m := by
  classical
  have hIcc : (Finset.Icc (-((m : ℤ) * Δ)) ((m : ℤ) * Δ)).card = 2 * m * Δ + 1 := by
    rw [Int.card_Icc]
    have he : ((m : ℤ) * Δ + 1 - -((m : ℤ) * Δ)) = ((2 * m * Δ + 1 : ℕ) : ℤ) := by
      push_cast; ring
    rw [he, Int.toNat_natCast]
  set Box : Finset (Fin m → ℤ) :=
    Fintype.piFinset (fun _ : Fin m => Finset.Icc (-((m : ℤ) * Δ)) ((m : ℤ) * Δ)) with hBox
  have hmaps : ∀ k ∈ (Finset.univ : Finset (Fin L)), p k ∈ Box := by
    intro k _
    rw [hBox, Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_Icc]
    have hk := hp k i
    rw [abs_le] at hk
    exact ⟨hk.1, hk.2⟩
  have hcard : Box.card = (2 * m * Δ + 1) ^ m := by
    rw [hBox, Fintype.card_piFinset]
    simp [hIcc]
  calc L = (Finset.univ : Finset (Fin L)).card := by simp
    _ = ∑ v ∈ Box, (Finset.univ.filter (fun k : Fin L => p k = v)).card :=
        Finset.card_eq_sum_card_fiberwise hmaps
    _ ≤ ∑ _v ∈ Box, m := Finset.sum_le_sum fun v _ => hmult v
    _ = Box.card * m := by rw [Finset.sum_const, smul_eq_mul]
    _ = (2 * m * Δ + 1) ^ m * m := by rw [hcard]
    _ = m * (2 * m * Δ + 1) ^ m := by ring
