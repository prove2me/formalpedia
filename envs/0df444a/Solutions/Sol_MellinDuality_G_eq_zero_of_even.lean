-- Prove2me | solution 1 for MellinDuality.G_eq_zero_of_even
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:56:14.957833+00:00
-- url     : https://prove2.me/submissions/bedb1a2f-3ef3-43d6-bf90-e2f1d2647408

module
public import Definitions.Def_MellinDuality_Defs
public import Definitions.Def_MellinDuality_Half
public import Theorems.Thm_MellinDuality_parSign_neg
public import Theorems.Thm_MellinDuality_sum_univ_eq_sum_half
public import Theorems.Thm_MellinDuality_apply_neg_of_even
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
variable {R : Type*} [CommRing R]
namespace MellinDuality
theorem _root_.solution (hp2 : p ≠ 2) (φ : MulChar (ZMod p) R) (hφ : φ (-1) = 1) : G φ = 0 := by
  unfold G
  rw [sum_univ_eq_sum_half hp2 _ (by simp [MulChar.map_zero])]
  refine sum_eq_zero fun n _ => ?_
  by_cases hn : n = 0
  · subst hn; simp [MulChar.map_zero]
  · rw [apply_neg_of_even φ hφ, parSign_neg hp2 hn]; push_cast; ring
end MellinDuality
