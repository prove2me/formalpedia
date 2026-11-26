-- Prove2me | solution 1 for MellinDuality.coset_lemma
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:58:27.238121+00:00
-- url     : https://prove2.me/submissions/640669e1-57af-42d0-9463-54086851f7b6

module
public import Definitions.Def_MellinDuality_Mellin
public import Definitions.Def_MellinDuality_Quartic
public import Theorems.Thm_MellinDuality_fam_eq_fibers

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
theorem _root_.solution (a : ZMod p) :
    (fam χ 2 a).re = ∑ u ∈ fiber χ 1, parSign u * parSign (a * u ^ 2) ∧
      (fam χ 2 a).im = ∑ u ∈ fiber χ gi, parSign u * parSign (a * u ^ 2) := by
  rw [fam_eq_fibers hp8 hχ]; exact ⟨rfl, rfl⟩
end MellinDuality
