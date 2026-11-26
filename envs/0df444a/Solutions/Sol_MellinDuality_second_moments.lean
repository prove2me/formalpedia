-- Prove2me | solution 1 for MellinDuality.second_moments
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:05:15.399393+00:00
-- url     : https://prove2.me/submissions/410819fc-762a-4095-95d6-77338728ccb2

module
public import Definitions.Def_MellinDuality
public import Definitions.Def_MellinDuality_Solution
public import Theorems.Thm_MellinDuality_second_moment_im
public import Theorems.Thm_MellinDuality_second_moment_re


set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace MellinDuality
theorem _root_.solution {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 5) (hχ : orderOf χ = 4) :
    ∑ a ∈ fiber χ 1, (fam χ 2 a).re ^ 2 =
        ∑ d ∈ fiber χ 1, multCorr (fiber χ 1) d * multCorr (fiber χ 1) (d ^ 2) ∧
      ∑ a ∈ fiber χ 1, (fam χ 2 a).im ^ 2 =
        ∑ d ∈ fiber χ 1, multCorr (fiber χ gi) d * multCorr (fiber χ 1) (d ^ 2) :=
  ⟨second_moment_re hp8 hχ, second_moment_im hp8 hχ⟩
end MellinDuality
