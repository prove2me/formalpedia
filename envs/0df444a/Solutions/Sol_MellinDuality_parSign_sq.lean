-- Prove2me | solution 1 for MellinDuality.parSign_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:03:00.469849+00:00
-- url     : https://prove2.me/submissions/c5b9bf2e-0e38-40a7-b393-15e041d75bb7

module
public import Definitions.Def_MellinDuality_Defs
public import Definitions.Def_MellinDuality_Half
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
omit hp
namespace MellinDuality
theorem _root_.solution (x : ZMod p) : parSign x * parSign x = 1 := by
  unfold parSign; rw [← pow_add, ← two_mul, pow_mul]; simp
end MellinDuality
