-- Prove2me | solution 1 for MellinDuality.ne_zero_of_mem_fiber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:46:14.796826+00:00
-- url     : https://prove2.me/submissions/d8a97fd4-d05e-4b7e-aa1e-5fc106d23df1

module
public import Definitions.Def_MellinDuality_Mellin
public import Definitions.Def_MellinDuality_Quartic
public import Theorems.Thm_MellinDuality_mem_fiber

set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt}
namespace MellinDuality
theorem _root_.solution {x : ZMod p} {z : GaussianInt} (hz : z ≠ 0) (hx : x ∈ fiber χ z) :
    x ≠ 0 := by
  rintro rfl; rw [mem_fiber, MulChar.map_zero] at hx; exact hz hx.symm
end MellinDuality
