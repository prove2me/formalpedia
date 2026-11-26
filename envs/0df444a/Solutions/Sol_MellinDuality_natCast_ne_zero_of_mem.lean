-- Prove2me | solution 1 for MellinDuality.natCast_ne_zero_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:45:25.85195+00:00
-- url     : https://prove2.me/submissions/089a1e92-5216-43fa-9a79-1409bd77c057

module
public import Definitions.Def_MellinDuality_Mellin
public import Definitions.Def_MellinDuality_Parseval

set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace MellinDuality
theorem _root_.solution {n : ℕ} (hn : n ∈ Icc 1 ((p - 1) / 2)) : (n : ZMod p) ≠ 0 := by
  rw [mem_Icc] at hn
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro h
  have := Nat.le_of_dvd (by omega) h
  have := hp.out.two_le
  omega
end MellinDuality
