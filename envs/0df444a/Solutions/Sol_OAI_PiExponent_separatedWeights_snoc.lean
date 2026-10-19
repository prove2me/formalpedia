-- Prove2me | solution 1 for OAI.PiExponent.separatedWeights_snoc
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T15:47:47.452516+00:00
-- url     : https://prove2.me/submissions/1f4341b7-dd51-4448-8b92-6c6012310862

import Mathlib
import Definitions.Def_PiExponent_DeterminantSetup

theorem solution
    (S : List ℕ → ℕ) {m : ℕ} (w : Fin m → ℕ) (x : ℕ) :
    OAI.PiExponent.separatedWeights S (Fin.snoc w x) ↔
      OAI.PiExponent.separatedWeights S w ∧ S (List.ofFn w) ≤ x := by
  unfold OAI.PiExponent.separatedWeights
  rw [Fin.forall_fin_succ']
  apply and_congr
  · apply forall_congr'
    intro i
    simp only [Fin.snoc_castSucc, Fin.coe_castSucc]
    have : (List.ofFn fun k : Fin i.val =>
        (Fin.snoc w x : Fin (m + 1) → ℕ) ⟨k.val, Nat.lt_trans k.isLt (Fin.castSucc i).isLt⟩) =
        List.ofFn fun k : Fin i.val => w ⟨k.val, Nat.lt_trans k.isLt i.isLt⟩ := by
      congr 1
      funext k
      have hk : k.val < m := Nat.lt_trans k.isLt i.isLt
      simp [Fin.snoc, hk]
    rw [this]
  · simp only [Fin.snoc_last, Fin.val_last]
    have : (List.ofFn fun k : Fin m =>
        (Fin.snoc w x : Fin (m + 1) → ℕ) ⟨k.val, Nat.lt_trans k.isLt (Fin.last m).isLt⟩) = List.ofFn w := by
      congr 1
      funext k
      simp [Fin.snoc, k.isLt]
    rw [this]
