-- Prove2me | solution 1 for MellinDuality.sum_fiber_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:54:16.579977+00:00
-- url     : https://prove2.me/submissions/8c0c3c1e-772a-4fbb-8373-4f1dcd6f1aff

module
public import Definitions.Def_MellinDuality_Mellin
public import Definitions.Def_MellinDuality_Quartic
public import Theorems.Thm_MellinDuality_mem_fiber
public import Theorems.Thm_MellinDuality_quartic_odd
public import Theorems.Thm_MellinDuality_apply_neg_of_odd
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
namespace MellinDuality
theorem _root_.solution {M : Type*} [AddCommMonoid M] (f : ZMod p → M) (z : GaussianInt) :
    ∑ x ∈ fiber χ (-z), f x = ∑ x ∈ fiber χ z, f (-x) := by
  have hodd := quartic_odd hp8 hχ
  refine sum_nbij' (fun x => -x) (fun x => -x) ?_ ?_ ?_ ?_ ?_
  · intro x hx; rw [mem_fiber] at *; rw [apply_neg_of_odd χ hodd, hx, neg_neg]
  · intro x hx; rw [mem_fiber] at *; rw [apply_neg_of_odd χ hodd, hx]
  · intro x _; simp
  · intro x _; simp
  · intro x _; simp
end MellinDuality
