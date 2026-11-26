-- Prove2me | solution 1 for MellinDuality.family_mean_values
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:05:12.879244+00:00
-- url     : https://prove2.me/submissions/e4082ef4-81bd-45b2-aaa1-b241b85306d9

module
public import Definitions.Def_MellinDuality
public import Definitions.Def_MellinDuality_Solution
public import Theorems.Thm_MellinDuality_family_means


set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace MellinDuality
theorem _root_.solution {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 5) (hχ : orderOf χ = 4) :
    (∑ a ∈ fiber χ 1, fam χ 2 a).re = sigma χ 1 ^ 2 ∧
      (∑ a ∈ fiber χ 1, fam χ 2 a).im = -(sigma χ 1 * sigma χ gi) :=
  family_means hp8 hχ
end MellinDuality
