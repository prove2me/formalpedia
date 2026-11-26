-- Prove2me | solution 1 for MellinDuality.fam_one_eq_bandSumPow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:45:19.351804+00:00
-- url     : https://prove2.me/submissions/079fea17-5435-4010-ad3f-e6d0e9a33ec5

module
public import Definitions.Def_MellinDuality_Half
public import Definitions.Def_MellinDuality_Mellin
public import Theorems.Thm_MellinDuality_odd_p


set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {R : Type*} [CommRing R]
namespace MellinDuality
theorem _root_.solution (hp2 : p ≠ 2) (χ : MulChar (ZMod p) R) {e : ℕ} (he : 1 ≤ e) :
    fam χ e 1 = bandSumPow χ e := by
  unfold fam bandSumPow bandSignE
  refine sum_congr rfl fun n _ => ?_
  congr 2
  rw [one_mul]
  have hval : (n ^ e).val = n.val ^ e % p := by
    rw [show (n ^ e : ZMod p) = ((n.val ^ e : ℕ) : ZMod p) by
      push_cast; rw [ZMod.natCast_zmod_val], ZMod.val_natCast]
  rw [hval]
  have hpo := odd_p hp2
  set v := n.val
  have hdec := Nat.div_add_mod (v ^ e) p
  have hpar : v ^ e % 2 = v % 2 := by
    rcases Nat.even_or_odd v with h | h
    · rw [Nat.even_iff.1 h, Nat.even_iff.1 (h.pow_of_ne_zero (by omega))]
    · rw [Nat.odd_iff.1 h, Nat.odd_iff.1 (h.pow)]
  have hpq : (p * (v ^ e / p)) % 2 = (v ^ e / p) % 2 := by
    rw [Nat.mul_mod, Nat.odd_iff.1 hpo, one_mul, Nat.mod_mod]
  rw [neg_one_pow_eq_pow_mod_two, neg_one_pow_eq_pow_mod_two (n := v ^ e / p)]
  congr 1
  omega
end MellinDuality
