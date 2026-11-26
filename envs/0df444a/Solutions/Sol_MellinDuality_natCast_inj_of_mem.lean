-- Prove2me | solution 1 for MellinDuality.natCast_inj_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:54:59.043539+00:00
-- url     : https://prove2.me/submissions/710bd4f6-4f56-4207-ae1c-337d5b0a1d20

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
theorem _root_.solution {n n' : ℕ} (hn : n ∈ Icc 1 ((p - 1) / 2))
    (hn' : n' ∈ Icc 1 ((p - 1) / 2)) : (n : ZMod p) = n' ↔ n = n' := by
  rw [mem_Icc] at hn hn'
  constructor
  · intro h
    have h' := congrArg ZMod.val h
    have := hp.out.two_le
    rwa [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at h'
  · rintro rfl; rfl
end MellinDuality
