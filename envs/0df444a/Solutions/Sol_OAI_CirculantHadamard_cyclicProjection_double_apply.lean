-- Prove2me | solution 1 for OAI.CirculantHadamard.cyclicProjection_double_apply
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T09:49:12.426979+00:00
-- url     : https://prove2.me/submissions/98dccbcd-f838-432e-8b31-f6ecab860f61

import Mathlib
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicProjection
theorem zdc_aux {m : ℕ} (hm : 0 < m) (h : m ∣ 2 * m)
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

open OAI OAI.CirculantHadamard
universe uA uB uR
open scoped BigOperators
variable {R : Type uR} [Semiring R]
theorem solution {m : ℕ} (hm : 0 < m) (h : m ∣ 2 * m)
    (f : CyclicRing.Elem R (2 * m)) (j : ZMod m) :
    (cyclicProjection R h f).coeff j =
      f.coeff (j.val : ZMod (2 * m)) + f.coeff ((j.val + m : ℕ) : ZMod (2 * m)) := by
  classical
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hf, hg]; abel
  | single a r =>
    have : NeZero m := ⟨by omega⟩
    have : NeZero (2 * m) := ⟨by omega⟩
    simp only [cyclicProjection_single, AddMonoidAlgebra.coeff_single]
    have hne : ((j.val : ℕ) : ZMod (2 * m)) ≠ ((j.val + m : ℕ) : ZMod (2 * m)) := by
      intro h2
      have := congrArg ZMod.val h2
      rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt (by have := ZMod.val_lt j; omega),
        Nat.mod_eq_of_lt (by have := ZMod.val_lt j; omega)] at this
      omega
    by_cases h1 : a = (j.val : ZMod (2 * m))
    · subst h1
      have : (ZMod.castHom h (ZMod m)) (j.val : ZMod (2 * m)) = j := (zdc_aux hm h _ j).2 (Or.inl rfl)
      rw [this, Finsupp.single_eq_same, Finsupp.single_eq_same, Finsupp.single_eq_of_ne (Ne.symm hne), add_zero]
    · by_cases h2 : a = ((j.val + m : ℕ) : ZMod (2 * m))
      · subst h2
        have : (ZMod.castHom h (ZMod m)) ((j.val + m : ℕ) : ZMod (2 * m)) = j :=
          (zdc_aux hm h _ j).2 (Or.inr rfl)
        rw [this, Finsupp.single_eq_same, Finsupp.single_eq_same, Finsupp.single_eq_of_ne (Ne.symm h1), zero_add]
      · have : (ZMod.castHom h (ZMod m)) a ≠ j := fun h3 =>
          ((zdc_aux hm h a j).1 h3).elim h1 h2
        rw [Finsupp.single_eq_of_ne (Ne.symm this), Finsupp.single_eq_of_ne (Ne.symm h1), Finsupp.single_eq_of_ne (Ne.symm h2), add_zero]
