-- Prove2me | solution 1 for OAI.CirculantHadamard.zmod_double_cast_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T09:39:10.676989+00:00
-- url     : https://prove2.me/submissions/cf7376d0-07fc-4f09-8247-8baae6185407

import Mathlib

theorem solution {m : ℕ} (hm : 0 < m) (h : m ∣ 2 * m)
    (x : ZMod (2 * m)) (j : ZMod m) :
    ZMod.castHom h (ZMod m) x = j ↔
      x = (j.val : ZMod (2 * m)) ∨ x = ((j.val + m : ℕ) : ZMod (2 * m)) := by
  haveI : NeZero m := ⟨hm.ne'⟩
  haveI : NeZero (2 * m) := ⟨by omega⟩
  have hx : x = ((x.val : ℕ) : ZMod (2 * m)) := (ZMod.natCast_zmod_val x).symm
  have hj : j = ((j.val : ℕ) : ZMod m) := (ZMod.natCast_zmod_val j).symm
  have hxv := ZMod.val_lt x
  have hjv := ZMod.val_lt j
  rw [hx]
  simp only [map_natCast]
  generalize x.val = a at hxv
  generalize hb : j.val = b at hjv
  rw [hj, hb]
  simp only [ZMod.natCast_eq_natCast_iff']
  rw [Nat.mod_eq_of_lt hxv, Nat.mod_eq_of_lt (by omega : b < 2 * m),
    Nat.mod_eq_of_lt (by omega : b + m < 2 * m), Nat.mod_eq_of_lt hjv]
  constructor
  · intro h1
    rcases lt_or_ge a m with h2 | h2
    · left; rw [Nat.mod_eq_of_lt h2] at h1; exact h1
    · right
      have : a % m = a - m := by
        rw [Nat.mod_eq_sub_mod h2, Nat.mod_eq_of_lt (by omega)]
      omega
  · rintro (h1 | h1)
    · subst h1; exact Nat.mod_eq_of_lt hjv
    · subst h1; simp [Nat.mod_eq_of_lt hjv]
