-- Prove2me | solution 1 for MellinDuality.totient_cast
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:47:28.785801+00:00
-- url     : https://prove2.me/submissions/d640554d-220d-4b15-8267-b0aaa1d96af3

module
public import Definitions.Def_MellinDuality_Half
public import Definitions.Def_MellinDuality_Mellin

set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace MellinDuality
theorem _root_.solution : ((Nat.totient p : ℕ) : ℂ) = (p : ℂ) - 1 := by
  rw [Nat.totient_prime hp.out, Nat.cast_sub hp.out.one_le, Nat.cast_one]
end MellinDuality
