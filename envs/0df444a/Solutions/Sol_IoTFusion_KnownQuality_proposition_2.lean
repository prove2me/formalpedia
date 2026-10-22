-- Prove2me | solution 1 for IoTFusion.KnownQuality.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T13:22:42.190072+00:00
-- url     : https://prove2.me/submissions/202c44c0-12e0-49ea-a159-15d6d0cffe59

import Mathlib
import Definitions.Def_IoTFusion_KnownQuality_Model

open IoTFusion.KnownQuality

theorem solution {n : ℕ} (P : IoTFusion.KnownQuality.Instance n) (i j : Fin n) (s : ℕ → ℝ) (x : ℝ) :
    (∀ k : ℕ, fam P i s (k + 1) j x =
      fam P i s k j x + stick (P.q i) (P.q j) * (if target P i s k = j then 1 else 0)) ∧
    (∀ k : ℕ, fam P i s k j x = psi1 P i j x + stick (P.q i) (P.q j) * (count P i s j k : ℝ)) := by
  have h1 : ∀ k : ℕ, fam P i s (k + 1) j x =
      fam P i s k j x + stick (P.q i) (P.q j) * (if target P i s k = j then 1 else 0) :=
    fun k => rfl
  refine ⟨h1, ?_⟩
  intro k
  induction k with
  | zero => simp [fam, count]
  | succ k ih =>
    rw [h1 k, ih]
    have hc : (count P i s j (k + 1) : ℝ) = (count P i s j k : ℝ) +
        (if target P i s k = j then 1 else 0) := by
      unfold count
      rw [Finset.range_add_one, Finset.filter_insert]
      split_ifs with h
      · rw [Finset.card_insert_of_notMem (by simp)]
        push_cast; ring
      · simp
    rw [hc]; ring
