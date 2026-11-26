-- Prove2me | solution 1 for MellinDuality.p_sub_one_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:49:46.710261+00:00
-- url     : https://prove2.me/submissions/61c8047e-e522-4fb8-a0ad-3b45f503af88

module
public import Definitions.Def_MellinDuality_Half
public import Definitions.Def_MellinDuality_Mellin
public import Theorems.Thm_MellinDuality_totient_cast

set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace MellinDuality
theorem _root_.solution : (p : ℂ) - 1 ≠ 0 := by
  rw [← totient_cast]; exact_mod_cast (Nat.totient_pos.2 hp.out.pos).ne'
end MellinDuality
