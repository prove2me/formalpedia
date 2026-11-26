-- Prove2me | solution 1 for MellinDuality.neg_one_pow_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:52:44.978507+00:00
-- url     : https://prove2.me/submissions/cb5b3d37-8dd1-4551-834f-de47282d78f5

module
public import Definitions.Def_MellinDuality_Defs
public import Definitions.Def_MellinDuality_Half
public import Theorems.Thm_MellinDuality_odd_p
public import Theorems.Thm_MellinDuality_gi_im
public import Theorems.Thm_MellinDuality_gi_re
attribute [local simp] MellinDuality.gi_im
attribute [local simp] MellinDuality.gi_re



set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace MellinDuality
theorem _root_.solution (hp2 : p ≠ 2) {v : ℕ} (hv : v ≤ p) :
    (-1 : ℤ) ^ (p - v) = -(-1) ^ v := by
  have ho := odd_p hp2
  calc (-1 : ℤ) ^ (p - v) = (-1) ^ (p - v) * ((-1) ^ v * (-1) ^ v) := by
        rw [← pow_add, ← two_mul, pow_mul]; simp
    _ = (-1) ^ (p - v + v) * (-1) ^ v := by ring
    _ = -(-1) ^ v := by rw [Nat.sub_add_cancel hv, ho.neg_one_pow]; ring
end MellinDuality
