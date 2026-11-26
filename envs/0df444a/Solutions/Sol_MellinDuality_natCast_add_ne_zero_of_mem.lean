-- Prove2me | solution 1 for MellinDuality.natCast_add_ne_zero_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:55:45.416619+00:00
-- url     : https://prove2.me/submissions/1807b9c5-ee6d-4472-9b52-a10e9801ec3f

module
public import Definitions.Def_MellinDuality_Pairs
public import Definitions.Def_MellinDuality_MeanSquare

set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace MellinDuality
theorem _root_.solution {n n' : ℕ} (hn : n ∈ Icc 1 ((p - 1) / 2))
    (hn' : n' ∈ Icc 1 ((p - 1) / 2)) : (n' : ZMod p) ≠ -(n : ZMod p) := by
  rw [mem_Icc] at hn hn'
  intro h
  have h' : ((n' + n : ℕ) : ZMod p) = 0 := by push_cast; rw [h]; ring
  rw [ZMod.natCast_eq_zero_iff] at h'
  have := Nat.le_of_dvd (by omega) h'
  omega
end MellinDuality
