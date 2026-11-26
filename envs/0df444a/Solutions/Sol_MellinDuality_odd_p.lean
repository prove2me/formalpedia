-- Prove2me | solution 1 for MellinDuality.odd_p
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:43:54.979727+00:00
-- url     : https://prove2.me/submissions/ab9f5d4d-ac26-4ef9-93a6-056b2e966590

module
public import Definitions.Def_MellinDuality_Defs
public import Definitions.Def_MellinDuality_Half

set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace MellinDuality
theorem _root_.solution (hp2 : p ≠ 2) : Odd p := hp.out.odd_of_ne_two hp2
end MellinDuality
