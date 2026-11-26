-- Prove2me | solution 1 for MellinDuality.quartic_terminal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:59:49.592109+00:00
-- url     : https://prove2.me/submissions/b39d1c15-07cd-483b-b5b1-1a36c7bd4d1e

module
public import Definitions.Def_MellinDuality_Mellin
public import Definitions.Def_MellinDuality_Quartic
public import Theorems.Thm_MellinDuality_hp2_of
public import Theorems.Thm_MellinDuality_quartic_odd
public import Theorems.Thm_MellinDuality_G_eq_two_gamma
public import Theorems.Thm_MellinDuality_G_mul_quad
public import Theorems.Thm_MellinDuality_exponent_collapse_one
public import Theorems.Thm_MellinDuality_exponent_collapse_two


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
theorem _root_.solution {m : ℕ} (hm : 1 ≤ m) (h4 : p - 1 ∣ 4 * m) :
    bandSumPow χ (2 * m) = if p - 1 ∣ 2 * m then -gamma χ else -star (gamma χ) := by
  have hp2 := hp2_of hp8
  have hodd := quartic_odd hp8 hχ
  apply mul_left_cancel₀ (by decide : (2 : GaussianInt) ≠ 0)
  split_ifs with h2
  · rw [exponent_collapse_one hp2 χ hodd hm h2, G_eq_two_gamma hp8 hχ]; ring
  · rw [exponent_collapse_two hp2 χ hodd h4 h2, G_mul_quad hχ, G_eq_two_gamma hp8 hχ,
      star_mul', star_ofNat]
    ring
end MellinDuality
