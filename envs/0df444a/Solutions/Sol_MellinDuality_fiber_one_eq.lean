-- Prove2me | solution 1 for MellinDuality.fiber_one_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:54:41.334478+00:00
-- url     : https://prove2.me/submissions/4e24c60b-f7db-4230-bd10-9b065da8dc61

module
public import Definitions.Def_MellinDuality_Mellin
public import Definitions.Def_MellinDuality_Quartic
public import Theorems.Thm_MellinDuality_mem_fiber
public import Theorems.Thm_MellinDuality_char_eq_one_iff
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
omit hp8
namespace MellinDuality
theorem _root_.solution : fiber χ 1 = univ.filter fun x : ZMod p => x ≠ 0 ∧ ∃ y, y ^ 4 = x := by
  ext x
  simp only [mem_fiber, mem_filter, mem_univ, true_and]
  constructor
  · intro h
    have hx : x ≠ 0 := by rintro rfl; rw [MulChar.map_zero] at h; exact zero_ne_one h
    exact ⟨hx, (char_eq_one_iff hχ hx).1 h⟩
  · rintro ⟨hx, hy⟩; exact (char_eq_one_iff hχ hx).2 hy
end MellinDuality
