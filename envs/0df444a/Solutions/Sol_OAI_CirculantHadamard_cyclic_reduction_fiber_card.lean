-- Prove2me | solution 1 for OAI.CirculantHadamard.cyclic_reduction_fiber_card
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T09:40:04.553867+00:00
-- url     : https://prove2.me/submissions/44302343-b6b5-4644-83e5-829eb38946f2

import Mathlib

theorem solution {n m d : ℕ} [NeZero n] [NeZero m]
    (hdiv : m ∣ n) (hn : n = m * d) (a : ZMod m) :
    Fintype.card {x : ZMod n // ZMod.castHom hdiv (ZMod m) x = a} = d := by
  classical
  set f := ZMod.castHom hdiv (ZMod m)
  have hsurj := ZMod.castHom_surjective hdiv
  have heq : ∀ b : ZMod m, (Finset.univ.filter fun x : ZMod n => f x = b).card =
      (Finset.univ.filter fun x : ZMod n => f x = a).card := fun b =>
    AddMonoidHom.card_fiber_eq_of_mem_range (f.toAddMonoidHom) (hsurj b) (hsurj a)
  have htot : (Finset.univ : Finset (ZMod n)).card =
      ∑ b : ZMod m, (Finset.univ.filter fun x : ZMod n => f x = b).card :=
    Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ (f x))
  simp_rw [heq] at htot
  simp only [Finset.card_univ, ZMod.card, Finset.sum_const, smul_eq_mul] at htot
  rw [Fintype.card_subtype]
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have h2 : m * d = m * (Finset.univ.filter fun x : ZMod n => f x = a).card := hn ▸ htot
  exact (Nat.eq_of_mul_eq_mul_left hm h2).symm
