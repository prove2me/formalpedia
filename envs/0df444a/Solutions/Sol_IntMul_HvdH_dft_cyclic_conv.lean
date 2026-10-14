-- Prove2me | solution 1 for IntMul.HvdH.dft_cyclic_conv
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-11T20:34:29.562925+00:00
-- url     : https://prove2.me/submissions/c2d80093-252b-4c61-b766-11fb5031c018

import Mathlib

open Finset

namespace IntMul.HvdH.Conv

/-- Cyclic convolution theorem for `ZMod.dft`. -/
theorem dft_cyclic_conv {N : ℕ} [NeZero N] (u v : ZMod N → ℂ) (k : ZMod N) :
    ZMod.dft (fun m => ∑ j, u j * v (m - j)) k = ZMod.dft u k * ZMod.dft v k := by
  simp only [ZMod.dft_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  symm
  refine Fintype.sum_equiv (Equiv.addLeft j) _ _ (fun l => ?_)
  simp only [Equiv.coe_addLeft, add_sub_cancel_left, add_mul, neg_add, AddChar.map_add_eq_mul]
  ring

/-- Agarwal–Cooley: the CRT isomorphism carries cyclic convolution on `ℤ/ab` to
two-dimensional cyclic convolution on `ℤ/a × ℤ/b`. -/
theorem crt_conv {R : Type*} [CommRing R] {a b : ℕ} [NeZero a] [NeZero b]
    (h : Nat.Coprime a b) (u v : ZMod (a * b) → R) (x : ZMod a × ZMod b) :
    ∑ j : ZMod (a * b), u j * v ((ZMod.chineseRemainder h).symm x - j) =
      ∑ y : ZMod a × ZMod b, u ((ZMod.chineseRemainder h).symm y) *
        v ((ZMod.chineseRemainder h).symm (x - y)) := by
  symm
  refine Fintype.sum_equiv (ZMod.chineseRemainder h).symm.toEquiv _ _ (fun y => ?_)
  simp [map_sub]

/-- Zero padding: if `u, v` vanish from index `n` on and `2n ≤ N + 1`, the length-`N` cyclic
convolution of `u, v` agrees with their linear (acyclic) convolution at every `k < N`. -/
theorem cyclic_conv_eq_linear {R : Type*} [CommRing R] {N n : ℕ} [NeZero N]
    (hN : 2 * n ≤ N + 1) (u v : ℕ → R) (hu : ∀ i, n ≤ i → u i = 0) (hv : ∀ i, n ≤ i → v i = 0)
    (k : ℕ) (hk : k < N) :
    ∑ j : ZMod N, u j.val * v ((k : ZMod N) - j).val = ∑ i ∈ range (k + 1), u i * v (k - i) := by
  have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have e1 : ∑ j : ZMod N, u j.val * v ((k : ZMod N) - j).val =
      ∑ i ∈ range N, u i * v ((k : ZMod N) - (i : ZMod N)).val := by
    refine Finset.sum_nbij' (fun j => j.val) (fun i => (i : ZMod N)) (fun j _ => ?_)
      (fun i _ => Finset.mem_univ _) (fun j _ => ZMod.natCast_zmod_val j) (fun i hi => ?_)
      (fun j _ => ?_)
    · exact Finset.mem_range.2 (ZMod.val_lt j)
    · rw [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.1 hi)]
    · simp only [ZMod.natCast_zmod_val]
  rw [e1, ← Finset.sum_range_add_sum_Ico _ (show k + 1 ≤ N by omega)]
  have e2 : ∑ i ∈ Ico (k + 1) N, u i * v ((k : ZMod N) - (i : ZMod N)).val = 0 := by
    refine Finset.sum_eq_zero (fun i hi => ?_)
    obtain ⟨hi1, hi2⟩ := Finset.mem_Ico.1 hi
    rcases le_or_gt n i with h | h
    · rw [hu i h, zero_mul]
    · have hc : (k : ZMod N) - (i : ZMod N) = ((N + k - i : ℕ) : ZMod N) := by
        rw [Nat.cast_sub (by omega), Nat.cast_add, ZMod.natCast_self, zero_add]
      rw [hc, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega), hv _ (by omega), mul_zero]
  rw [e2, add_zero]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hi' := Finset.mem_range.1 hi
  have hc : (k : ZMod N) - (i : ZMod N) = ((k - i : ℕ) : ZMod N) := by
    rw [Nat.cast_sub (by omega)]
  rw [hc, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]

end IntMul.HvdH.Conv

theorem solution {N : ℕ} [NeZero N] (u v : ZMod N → ℂ) (k : ZMod N) :
    ZMod.dft (fun m => ∑ j, u j * v (m - j)) k = ZMod.dft u k * ZMod.dft v k :=
  IntMul.HvdH.Conv.dft_cyclic_conv u v k
