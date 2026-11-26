-- Prove2me | solution 1 for MellinDuality.coset_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:04:24.544417+00:00
-- url     : https://prove2.me/submissions/e6c9cee9-73f6-4ee2-9e8d-9e6b58c87f4f

module
public import Definitions.Def_MellinDuality
public import Definitions.Def_MellinDuality_Solution
public import Theorems.Thm_MellinDuality_coset_lemma


set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace MellinDuality
theorem _root_.solution {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 5) (hχ : orderOf χ = 4)
    (a : ZMod p) :
    (fam χ 2 a).re = ∑ u ∈ fiber χ 1, parSign u * parSign (a * u ^ 2) ∧
      (fam χ 2 a).im = ∑ u ∈ fiber χ gi, parSign u * parSign (a * u ^ 2) :=
  coset_lemma hp8 hχ a
end MellinDuality
