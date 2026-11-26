-- Prove2me | solution 1 for MellinDuality.cosets_as_fibers
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:04:23.928013+00:00
-- url     : https://prove2.me/submissions/604461a9-3de4-4374-9dcc-f948694b3a9f

module
public import Definitions.Def_MellinDuality
public import Definitions.Def_MellinDuality_Solution
public import Theorems.Thm_MellinDuality_fiber_gi_eq
public import Theorems.Thm_MellinDuality_fiber_one_eq
public import Theorems.Thm_MellinDuality_quartic_odd


set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace MellinDuality
theorem _root_.solution {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 5) (hχ : orderOf χ = 4) :
    χ (-1) = -1 ∧ fiber χ 1 = univ.filter (fun x : ZMod p => x ≠ 0 ∧ ∃ y, y ^ 4 = x) ∧
      (χ 2 = gi → fiber χ gi = (fiber χ 1).image (2 * ·)) :=
  ⟨quartic_odd hp8 hχ, fiber_one_eq hχ, fun hpin => fiber_gi_eq hp8 hpin⟩
end MellinDuality
