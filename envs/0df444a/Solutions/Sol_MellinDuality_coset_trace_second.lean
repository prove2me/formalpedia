-- Prove2me | solution 1 for MellinDuality.coset_trace_second
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:04:58.246134+00:00
-- url     : https://prove2.me/submissions/64fb28f8-577a-4113-9b91-c31e28c80e2c

module
public import Definitions.Def_MellinDuality
public import Definitions.Def_MellinDuality_Solution
public import Theorems.Thm_MellinDuality_coset_trace_second_form


set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace MellinDuality
theorem _root_.solution {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 5) (hχ : orderOf χ = 4)
    {c : GaussianInt} (hc : c = 1 ∨ c = gi ∨ c = -1 ∨ c = -gi) :
    2 * ∑ a ∈ fiber χ c, fam χ 2 a =
      star c * (gamma χ * star (gamma χ)) + c * star (gamma χ) ^ 2 :=
  coset_trace_second_form hp8 hχ hc
end MellinDuality
