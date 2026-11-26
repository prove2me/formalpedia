-- Prove2me | solution 1 for MellinDuality.family_means
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:00:29.581419+00:00
-- url     : https://prove2.me/submissions/d1635501-fa8a-480c-a5c1-fca070ecb778

module
public import Definitions.Def_MellinDuality_Mellin
public import Definitions.Def_MellinDuality_Quartic
public import Theorems.Thm_MellinDuality_sum_fiber_fam
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
variable (hp8 : p % 8 = 5) (hχ : orderOf χ = 4)
include hp8 hχ
namespace MellinDuality
theorem _root_.solution :
    (∑ a ∈ fiber χ 1, fam χ 2 a).re = sigma χ 1 ^ 2 ∧
      (∑ a ∈ fiber χ 1, fam χ 2 a).im = -(sigma χ 1 * sigma χ gi) := by
  rw [sum_fiber_fam hp8 hχ one_ne_zero]
  constructor <;> simp [gamma, sq]
end MellinDuality
