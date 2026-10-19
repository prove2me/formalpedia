-- Prove2me | solution 1 for OAI.FiniteCircle.get_flatMap_uniform
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T17:18:46.768478+00:00
-- url     : https://prove2.me/submissions/3b7225fb-f97e-4ad8-af0d-be0388a8aa46

import Mathlib.Data.List.Basic

theorem solution {α β : Type*} (xs : List α) (f : α → List β) {L : ℕ}
    (hL : 0 < L) (hl : ∀ a ∈ xs, (f a).length = L)
    (k : Fin (xs.flatMap f).length) :
    ∃ (i : Fin xs.length) (b : Fin (f (xs.get i)).length),
      i.val = k.val/L ∧ b.val = k.val%L ∧ (xs.flatMap f).get k = (f (xs.get i)).get b := by
  induction xs with
  | nil => exact Fin.elim0 k
  | cons a xs ih =>
    have ha : (f a).length = L := hl a (by simp)
    have hs : ∀ b ∈ xs, (f b).length = L := fun b hb => hl b (by simp [hb])
    by_cases hk : k.val < L
    · refine ⟨⟨0, by simp⟩, ⟨k.val, by simpa [ha] using hk⟩, ?_, ?_, ?_⟩
      · simp [Nat.div_eq_of_lt hk]
      · simp [Nat.mod_eq_of_lt hk]
      · simp only [List.flatMap_cons, List.get_eq_getElem, List.getElem_cons_zero]
        exact List.getElem_append_left (by simpa [ha] using hk)
    · have hk' : k.val - L < (xs.flatMap f).length := by
        have h := k.isLt
        simp only [List.flatMap_cons, List.length_append, ha] at h
        omega
      obtain ⟨i, b, hi, hb, he⟩ := ih hs ⟨k.val - L, hk'⟩
      have hsum : k.val = (k.val - L) + L := by omega
      refine ⟨⟨i.val + 1, by simp⟩, b, ?_, ?_, ?_⟩
      · rw [hsum, Nat.add_div_right _ hL]
        exact congrArg (fun n => n + 1) hi
      · rw [hsum, Nat.add_mod_right]
        exact hb
      · simp only [List.flatMap_cons, List.get_eq_getElem, List.getElem_cons_succ]
        rw [List.getElem_append_right (by omega)]
        simpa only [ha, List.get_eq_getElem] using he
