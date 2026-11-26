-- Prove2me | solution 1 for MellinDuality.sum_univ_fibers
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:55:35.121004+00:00
-- url     : https://prove2.me/submissions/079a6723-6fc1-4623-9af9-6175b5524b27

module
public import Definitions.Def_MellinDuality_Mellin
public import Definitions.Def_MellinDuality_Quartic
public import Theorems.Thm_MellinDuality_char_ne_zero
public import Theorems.Thm_MellinDuality_gi_im
public import Theorems.Thm_MellinDuality_gi_re
public import Theorems.Thm_MellinDuality_quartic_values
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
theorem _root_.solution {M : Type*} [AddCommMonoid M] (f : ZMod p → M) (h0 : f 0 = 0) :
    ∑ x, f x = ∑ x ∈ fiber χ 1, f x + ∑ x ∈ fiber χ gi, f x + ∑ x ∈ fiber χ (-1), f x +
      ∑ x ∈ fiber χ (-gi), f x := by
  have hmaps : ∀ x ∈ (univ : Finset (ZMod p)),
      χ x ∈ ({0, 1, gi, -1, -gi} : Finset GaussianInt) := by
    intro x _
    by_cases hx : x = 0
    · simp [hx, MulChar.map_zero]
    · rcases quartic_values χ hχ hx with h | h | h | h <;> simp [h]
  rw [← sum_fiberwise_of_maps_to hmaps, sum_insert (by decide), sum_insert (by decide),
    sum_insert (by decide), sum_insert (by decide), sum_singleton]
  have hz : ∑ x ∈ univ.filter (fun x => χ x = 0), f x = 0 := by
    refine sum_eq_zero fun x hx => ?_
    have hx0 : x = 0 := by
      by_contra h; exact char_ne_zero hχ h (mem_filter.1 hx).2
    rw [hx0, h0]
  rw [hz, zero_add]
  simp only [fiber, add_assoc]
end MellinDuality
