-- Prove2me | solution 1 for MellinDuality.hp2_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:45:08.086404+00:00
-- url     : https://prove2.me/submissions/9bdb23b8-0d8e-458c-bda4-0e425b74facb

module
public import Definitions.Def_MellinDuality_Mellin
public import Definitions.Def_MellinDuality_Quartic

set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
omit hp
namespace MellinDuality
theorem _root_.solution (hp8 : p % 8 = 5) : p ≠ 2 := by omega
end MellinDuality
