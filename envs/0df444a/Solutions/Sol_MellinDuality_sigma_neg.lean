-- Prove2me | solution 1 for MellinDuality.sigma_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:55:56.021529+00:00
-- url     : https://prove2.me/submissions/879a93cb-af90-4553-be83-d5d95c89f034

module
public import Definitions.Def_MellinDuality_Mellin
public import Definitions.Def_MellinDuality_Quartic
public import Theorems.Thm_MellinDuality_hp2_of
public import Theorems.Thm_MellinDuality_ne_zero_of_mem_fiber
public import Theorems.Thm_MellinDuality_sum_fiber_neg
public import Theorems.Thm_MellinDuality_parSign_neg


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
theorem _root_.solution {z : GaussianInt} (hz : z ≠ 0) : sigma χ (-z) = -sigma χ z := by
  unfold sigma
  rw [sum_fiber_neg hp8 hχ, ← sum_neg_distrib]
  exact sum_congr rfl fun x hx => parSign_neg (hp2_of hp8) (ne_zero_of_mem_fiber hz hx)
end MellinDuality
