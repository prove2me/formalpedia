-- Prove2me | solution 1 for OAI.CirculantHadamard.order_even_of_sign_norm
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T09:51:52.775711+00:00
-- url     : https://prove2.me/submissions/c7cafbc5-e3a8-4e45-b784-2ad5201416a1

import Mathlib
import Definitions.Def_CirculantHadamard
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Basic
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Witnesses
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_MatrixBridge
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicRing
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicNorm

open OAI OAI.CirculantHadamard
universe uIota
open scoped BigOperators
theorem solution {n : ℕ} [NeZero n] (hn : 1 < n)
    (f : CyclicRing.Elem ℤ n) (hsign : CyclicSignRow f)
    (hnorm : f * CyclicRing.ringStar f = CyclicRing.scalar n (n : ℤ)) :
    Even n := by
  have h1 : (1 : ZMod n) ≠ 0 := by
    intro h
    have := ZMod.val_one'' (n := n) (by omega)
    rw [h, ZMod.val_zero] at this; exact zero_ne_one this
  have hc := congrArg (fun g => AddMonoidAlgebra.coeff g (1 : ZMod n)) hnorm
  simp only [CyclicRing.group_mul_apply, CyclicRing.ringStar_apply, CyclicRing.scalar_apply,
    if_neg h1, star_trivial] at hc
  have h2 := congrArg (Int.cast : ℤ → ZMod 2) hc
  push_cast at h2
  have hone : ∀ j : ZMod n, ((f.coeff j * f.coeff (-(1 - j)) : ℤ) : ZMod 2) = 1 := by
    intro j
    rcases hsign j with h | h <;> rcases hsign (-(1 - j)) with h' | h' <;>
      · rw [h, h']; decide
  simp only [Int.cast_mul] at hone
  rw [Finset.sum_congr rfl (fun j _ => hone j), Finset.sum_const, Finset.card_univ, ZMod.card,
    nsmul_eq_mul, mul_one] at h2
  exact (ZMod.natCast_eq_zero_iff_even).1 h2
