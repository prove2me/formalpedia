-- Prove2me | solution 1 for LatinQuarter.product_eq_zero_of_card_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:21:26.257048+00:00
-- url     : https://prove2.me/submissions/9afd5b7c-64f4-46e9-a11c-d51140f16937

module
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.Algebra.Algebra.Operations
public import Definitions.Def_LeanPool_LatinQuarter_SquareZero
public import Theorems.Thm_LatinQuarter_product_eq_zero_of_repeated_square_zero

set_option autoImplicit true
@[expose] public section
public section
open LatinQuarter
open scoped BigOperators Pointwise
variable {R : Type*} [CommRing R]
namespace LatinQuarter
theorem _root_.solution
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (z : κ → R) (hz : ∀ j, z j * z j = 0)
    (f : ι → κ) (hcard : Fintype.card κ < Fintype.card ι) :
    ∏ i, z (f i) = 0 := by
  have hn : ¬ Function.Injective f := by
    intro hf
    exact (not_le_of_gt hcard) (Fintype.card_le_of_injective f hf)
  simp only [Function.Injective, not_forall] at hn
  obtain ⟨a, b, hab⟩ := hn
  have heq : f a = f b := by tauto
  have hne : a ≠ b := by tauto
  exact product_eq_zero_of_repeated_square_zero (fun i => z (f i))
    hne (congrArg z heq) (hz (f a))
end LatinQuarter
