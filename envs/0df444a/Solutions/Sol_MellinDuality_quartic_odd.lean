-- Prove2me | solution 1 for MellinDuality.quartic_odd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:53:08.413517+00:00
-- url     : https://prove2.me/submissions/07160b45-12c2-44cf-89a5-28afc1b87028

module
public import Definitions.Def_MellinDuality_Mellin
public import Definitions.Def_MellinDuality_Quartic
public import Theorems.Thm_MellinDuality_quartic_apply_neg_one


set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt}
variable (hp8 : p % 8 = 5) (hχ : orderOf χ = 4)
include hp8 hχ
namespace MellinDuality
theorem _root_.solution : χ (-1) = -1 := quartic_apply_neg_one χ hχ hp8
end MellinDuality
