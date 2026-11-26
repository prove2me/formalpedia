-- Prove2me | solution 1 for MellinDuality.sum_fiber_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:46:18.566797+00:00
-- url     : https://prove2.me/submissions/9ab6022d-c25e-44c0-bf26-9852f05841ac

module
public import Definitions.Def_MellinDuality_Mellin
public import Definitions.Def_MellinDuality_Quartic
public import Theorems.Thm_MellinDuality_mem_fiber
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
namespace MellinDuality
theorem _root_.solution {M : Type*} [AddCommMonoid M] (f : ZMod p → M) (c : GaussianInt)
    {w : ZMod p} (hw : w ≠ 0) (hwu : χ w * χ w⁻¹ = 1) :
    ∑ a ∈ fiber χ c, f (a * w) = ∑ b ∈ fiber χ (c * χ w), f b := by
  refine sum_nbij' (· * w) (· * w⁻¹) ?_ ?_ ?_ ?_ ?_
  · intro a ha; rw [mem_fiber] at *; rw [map_mul, ha]
  · intro b hb
    rw [mem_fiber] at *
    rw [map_mul, hb, mul_assoc, hwu, mul_one]
  · intro a _; simp [mul_assoc, mul_inv_cancel₀ hw]
  · intro b _; simp [mul_assoc, inv_mul_cancel₀ hw]
  · intro a _; rfl
end MellinDuality
