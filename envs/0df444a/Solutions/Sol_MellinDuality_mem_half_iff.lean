-- Prove2me | solution 1 for MellinDuality.mem_half_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:43:56.411049+00:00
-- url     : https://prove2.me/submissions/095a787d-9cfe-4fc4-9d95-a33a95dbded3

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
namespace MellinDuality
theorem _root_.solution {x : ZMod p} : x ∈ half p ↔ 2 * x.val < p := by simp [half]
end MellinDuality
