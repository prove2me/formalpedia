-- Prove2me | solution 1 for MellinDuality.coset_trace_values
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:04:57.66683+00:00
-- url     : https://prove2.me/submissions/2a161ea0-9088-4fa3-bdb2-f59241f4ab99

module
public import Definitions.Def_MellinDuality
public import Definitions.Def_MellinDuality_Solution
public import Theorems.Thm_MellinDuality_coset_trace


set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace MellinDuality
theorem _root_.solution {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 5) (hχ : orderOf χ = 4)
    {c : GaussianInt} (hc : c = 1 ∨ c = gi ∨ c = -1 ∨ c = -gi) :
    ∑ a ∈ fiber χ c, fam χ 2 a = ((star c * gamma χ).re : GaussianInt) * star (gamma χ) :=
  coset_trace hp8 hχ hc
end MellinDuality
