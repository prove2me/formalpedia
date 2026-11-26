-- Prove2me | solution 1 for MellinDuality.fam_eq_fibers
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:57:16.910373+00:00
-- url     : https://prove2.me/submissions/6c642a4d-73d8-4e71-96ae-c028242e48bd

module
public import Definitions.Def_MellinDuality_Mellin
public import Definitions.Def_MellinDuality_Quartic
public import Theorems.Thm_MellinDuality_hp2_of
public import Theorems.Thm_MellinDuality_mem_fiber
public import Theorems.Thm_MellinDuality_quartic_odd
public import Theorems.Thm_MellinDuality_sum_fiber_neg
public import Theorems.Thm_MellinDuality_sum_univ_fibers
public import Theorems.Thm_MellinDuality_apply_neg_of_odd
public import Theorems.Thm_MellinDuality_fam_eq
public import Theorems.Thm_MellinDuality_gi_im
public import Theorems.Thm_MellinDuality_gi_re
public import Theorems.Thm_MellinDuality_parSign_neg
public import Theorems.Thm_MellinDuality_sum_univ_eq_sum_half
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
theorem _root_.solution (a : ZMod p) :
    fam χ 2 a = ⟨sqCorr (fiber χ 1) a, sqCorr (fiber χ gi) a⟩ := by
  have hodd := quartic_odd hp8 hχ
  have hp2 := hp2_of hp8
  set g : ZMod p → GaussianInt := fun x =>
    χ x * (parSign x : GaussianInt) * (parSign (a * x ^ 2) : GaussianInt) with hg
  have hg0 : g 0 = 0 := by simp [g, MulChar.map_zero]
  have hgneg : ∀ x, g (-x) = g x := by
    intro x
    by_cases hx : x = 0
    · simp [hx]
    · simp only [g, apply_neg_of_odd χ hodd, parSign_neg hp2 hx, neg_sq]; push_cast; ring
  have h1 : (2 : GaussianInt) * fam χ 2 a = ∑ x, g x := by
    rw [sum_univ_eq_sum_half hp2 g hg0, fam_eq, mul_sum]
    exact sum_congr rfl fun n _ => by rw [hgneg]; simp only [g]; ring
  have h2 : ∑ x, g x = 2 * (∑ u ∈ fiber χ 1, g u + ∑ u ∈ fiber χ gi, g u) := by
    rw [sum_univ_fibers hχ g hg0, sum_fiber_neg hp8 hχ g 1, sum_fiber_neg hp8 hχ g gi]
    simp_rw [hgneg]; ring
  have h3 : ∑ u ∈ fiber χ 1, g u = ((sqCorr (fiber χ 1) a : ℤ) : GaussianInt) := by
    unfold sqCorr; push_cast
    exact sum_congr rfl fun u hu => by simp only [g, mem_fiber.1 hu]; ring
  have h4 : ∑ u ∈ fiber χ gi, g u = gi * ((sqCorr (fiber χ gi) a : ℤ) : GaussianInt) := by
    unfold sqCorr; push_cast; rw [mul_sum]
    exact sum_congr rfl fun u hu => by simp only [g, mem_fiber.1 hu]; ring
  have key := h1.trans h2
  rw [h3, h4] at key
  have := mul_left_cancel₀ (by decide : (2 : GaussianInt) ≠ 0) key
  rw [this]
  ext <;> simp [gi]
end MellinDuality
