-- Prove2me | solution 1 for MellinDuality.conjugate_dynamics
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:00:10.684365+00:00
-- url     : https://prove2.me/submissions/86a1fe3f-d3c5-44d1-912b-2fe87c96f8ef

module
public import Definitions.Def_MellinDuality_Mellin
public import Definitions.Def_MellinDuality_Quartic
public import Theorems.Thm_MellinDuality_mem_fiber
public import Theorems.Thm_MellinDuality_ne_zero_of_mem_fiber
public import Theorems.Thm_MellinDuality_sum_fiber_mul
public import Theorems.Thm_MellinDuality_char_mul_char_inv
public import Theorems.Thm_MellinDuality_coset_lemma

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
theorem _root_.solution {a : ZMod p} (ha : a ∈ fiber χ 1) :
    (fam χ 2 a).re = ∑ v ∈ fiber χ 1, parSign (a⁻¹ * v) * parSign (a⁻¹ * v ^ 2) := by
  have ha0 := ne_zero_of_mem_fiber one_ne_zero ha
  have hinv : χ a⁻¹ = 1 := by
    have := char_mul_char_inv (χ := χ) ha0; rwa [mem_fiber.1 ha, one_mul] at this
  rw [(coset_lemma hp8 hχ a).1]
  have := sum_fiber_mul (χ := χ) (fun u => parSign u * parSign (a * u ^ 2)) 1
    (inv_ne_zero ha0) (by rw [inv_inv, mul_comm]; exact char_mul_char_inv ha0)
  rw [hinv, mul_one] at this
  rw [← this]
  refine sum_congr rfl fun v _ => ?_
  rw [mul_comm v a⁻¹]
  congr 2
  field_simp
end MellinDuality
