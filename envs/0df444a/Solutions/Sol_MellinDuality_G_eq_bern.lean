-- Prove2me | solution 1 for MellinDuality.G_eq_bern
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:59:09.051111+00:00
-- url     : https://prove2.me/submissions/cba76371-da85-4ab8-80f2-3c62efb2180b

module
public import Definitions.Def_MellinDuality_Half
public import Definitions.Def_MellinDuality_Mellin
public import Theorems.Thm_MellinDuality_bernoulli_form


set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace MellinDuality
theorem _root_.solution (hp2 : p ≠ 2) (φ : DirichletCharacter ℂ p) (hφ : φ (-1) = -1) :
    G φ = 2 * (1 - 2 * φ 2) * bern φ := by
  have h := bernoulli_form hp2 φ hφ
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  unfold bern
  field_simp
  linear_combination h
end MellinDuality
