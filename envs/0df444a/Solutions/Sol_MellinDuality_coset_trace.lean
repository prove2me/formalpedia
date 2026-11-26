-- Prove2me | solution 1 for MellinDuality.coset_trace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:00:26.153542+00:00
-- url     : https://prove2.me/submissions/35c40ef2-7d7e-44d9-8592-dc705e048029

module
public import Definitions.Def_MellinDuality_Mellin
public import Definitions.Def_MellinDuality_Quartic
public import Theorems.Thm_MellinDuality_sigma_eq_re
public import Theorems.Thm_MellinDuality_sum_fiber_fam

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
    ∑ a ∈ fiber χ c, fam χ 2 a = ((star c * gamma χ).re : GaussianInt) * star (gamma χ) := by
  have hc0 : c ≠ 0 := by rcases hc with rfl | rfl | rfl | rfl <;> decide
  rw [sum_fiber_fam hp8 hχ hc0, sigma_eq_re hp8 hχ hc]
end MellinDuality
