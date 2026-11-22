-- Prove2me | solution 1 for LatinQuarter.coeff_allTags_product
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:22:33.99533+00:00
-- url     : https://prove2.me/submissions/4750c727-56bf-4b1d-906c-f067acfe663f

module
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Definitions.Def_LeanPool_LatinQuarter_Tags
public import Theorems.Thm_LatinQuarter_tag_sq
public import Theorems.Thm_LatinQuarter_allTagsExponent_apply
public import Theorems.Thm_LatinQuarter_allTagsExponent_support
attribute [local simp] LatinQuarter.tag_sq
attribute [local simp] LatinQuarter.allTagsExponent_apply
attribute [local simp] LatinQuarter.allTagsExponent_support

set_option autoImplicit true
@[expose] public section
public section
open LatinQuarter
open scoped BigOperators
open MvPolynomial
namespace LatinQuarter
theorem _root_.solution {κ : Type*} [Fintype κ] :
    (∏ j : κ, X j : MvPolynomial κ (ZMod 2)).coeff (allTagsExponent κ) = 1 := by
  classical
  have hp := prod_X_pow_eq_monomial (R := ZMod 2) (s := allTagsExponent κ)
  simp only [allTagsExponent_support, allTagsExponent_apply, pow_one] at hp
  rw [hp]
  simp
end LatinQuarter
