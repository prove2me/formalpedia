-- Prove2me | solution 1 for MellinDuality.multiplier_constant_bern
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:03:20.998536+00:00
-- url     : https://prove2.me/submissions/04b9cd47-5177-476b-9687-78cf3f738ef7

module
public import Definitions.Def_MellinDuality
public import Definitions.Def_MellinDuality_Solution
public import Theorems.Thm_MellinDuality_G_eq_bern


set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace MellinDuality
theorem _root_.solution (hp2 : p ≠ 2) (φ : DirichletCharacter ℂ p) (hφ : φ (-1) = -1) :
    G φ = 2 * (1 - 2 * φ 2) * bern φ :=
  G_eq_bern hp2 φ hφ
end MellinDuality
