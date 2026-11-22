-- Prove2me | solution 1 for LongGapsBetweenPrimes.exists_linear_roots
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:12:12.486194+00:00
-- url     : https://prove2.me/submissions/0d9b9bb0-5d3c-41b5-883b-72c60ecbda60

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {p k Q b : ℕ} (hp : p.Prime) (hQ : Q.Coprime p)
    (s : Fin k → ℕ) (hs : Function.Injective s) (hsmall : ∀ i, s i < p) :
    ∃ root : Fin k → Fin p, Function.Injective root ∧
      ∀ n i, n % p = (root i).val → p ∣ b + Q * (n + 1) + s i := by
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have hQ' : (Q : ZMod p) ≠ 0 := ((ZMod.isUnit_iff_coprime Q p).mpr hQ).ne_zero
  let root (i : Fin k) : Fin p :=
    ⟨(-(b + Q + s i : ZMod p) / Q).val, ZMod.val_lt _⟩
  refine ⟨root, ?_, ?_⟩
  · intro i j hij
    have h := congrArg (fun a : Fin p => (a.val : ZMod p) * Q) hij
    simp only [root, ZMod.natCast_zmod_val, div_mul_cancel₀ _ hQ', neg_inj,
      add_right_inj] at h
    apply hs
    simpa only [Nat.ModEq, Nat.mod_eq_of_lt (hsmall i), Nat.mod_eq_of_lt (hsmall j)]
      using (ZMod.natCast_eq_natCast_iff (s i) (s j) p).mp h
  · intro n i hn
    have hn' : (n : ZMod p) = -(b + Q + s i : ZMod p) / Q := by
      have h := congrArg (fun a : ℕ => (a : ZMod p)) hn
      simpa only [root, ZMod.natCast_mod, ZMod.natCast_zmod_val] using h
    apply (ZMod.natCast_eq_zero_iff _ p).mp
    push_cast
    rw [hn']
    field_simp
    ring
end LongGapsBetweenPrimes
