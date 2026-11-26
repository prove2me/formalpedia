-- Prove2me | solution 1 for MellinDuality.mem_fiber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:45:05.541603+00:00
-- url     : https://prove2.me/submissions/ab27c190-4fd2-4b29-bf76-d0bcd5eca7a4

module
public import Definitions.Def_MellinDuality_Mellin
public import Definitions.Def_MellinDuality_Quartic
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
variable {χ : MulChar (ZMod p) GaussianInt}
namespace MellinDuality
theorem _root_.solution {x : ZMod p} {z : GaussianInt} : x ∈ fiber χ z ↔ χ x = z := by simp [fiber]
end MellinDuality
