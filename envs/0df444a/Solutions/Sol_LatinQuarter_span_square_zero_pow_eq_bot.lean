-- Prove2me | solution 1 for LatinQuarter.span_square_zero_pow_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:22:04.328292+00:00
-- url     : https://prove2.me/submissions/9e95bd91-2b62-4e82-b80c-865c8d46e5b1

module
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.Algebra.Algebra.Operations
public import Definitions.Def_LeanPool_LatinQuarter_SquareZero
public import Theorems.Thm_LatinQuarter_product_eq_zero_of_card_lt

set_option autoImplicit true
@[expose] public section
public section
open LatinQuarter
open scoped BigOperators Pointwise
variable {R : Type*} [CommRing R]
namespace LatinQuarter
theorem _root_.solution
    {κ : Type*} [Fintype κ] (z : κ → R)
    (hz : ∀ j, z j * z j = 0) {d : ℕ}
    (hd : Fintype.card κ < d) :
    Ideal.span (Set.range z) ^ d = ⊥ := by
  classical
  apply le_antisymm _ bot_le
  change (Submodule.span R (Set.range z)) ^ d ≤ ⊥
  rw [Submodule.span_pow]
  apply Submodule.span_le.mpr
  intro x hx
  obtain ⟨f, hf, rfl⟩ := Set.mem_pow_iff_prod.mp hx
  choose g hg using hf
  have hfz : f = fun i => z (g i) := funext (fun i => (hg i).symm)
  rw [hfz]
  have heq := product_eq_zero_of_card_lt z hz g (by simpa using hd)
  simpa only [Submodule.mem_bot, SetLike.mem_coe] using heq
end LatinQuarter
