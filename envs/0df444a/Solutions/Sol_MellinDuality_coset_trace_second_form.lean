-- Prove2me | solution 1 for MellinDuality.coset_trace_second_form
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:01:35.550702+00:00
-- url     : https://prove2.me/submissions/3d18e40a-2f69-4b91-8ed4-3511ad7318b6

module
public import Definitions.Def_MellinDuality_Mellin
public import Definitions.Def_MellinDuality_Quartic
public import Theorems.Thm_MellinDuality_coset_trace
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
theorem _root_.solution {c : GaussianInt} (hc : c = 1 ∨ c = gi ∨ c = -1 ∨ c = -gi) :
    2 * ∑ a ∈ fiber χ c, fam χ 2 a =
      star c * (gamma χ * star (gamma χ)) + c * star (gamma χ) ^ 2 := by
  rw [coset_trace hp8 hχ hc]
  have hre : ∀ x : GaussianInt, 2 * ((x.re : ℤ) : GaussianInt) = x + star x := by
    intro x; ext <;> simp [two_mul]
  rw [← mul_assoc, hre, star_mul', star_star]
  ring
end MellinDuality
