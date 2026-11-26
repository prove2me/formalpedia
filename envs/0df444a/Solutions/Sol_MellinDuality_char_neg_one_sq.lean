-- Prove2me | solution 1 for MellinDuality.char_neg_one_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:56:33.628522+00:00
-- url     : https://prove2.me/submissions/e6f35fbe-6737-4ae6-8c17-612cabb54965

module
public import Definitions.Def_MellinDuality_Pairs
public import Definitions.Def_MellinDuality_MeanSquare
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
namespace MellinDuality
theorem _root_.solution (ψ : DirichletCharacter ℂ p) : ψ (-1) * ψ (-1) = 1 := by
  rw [← map_mul]; simp
end MellinDuality
