-- Prove2me | solution 1 for LatinQuarter.allTagsExponent_degree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:22:34.874542+00:00
-- url     : https://prove2.me/submissions/9d463c46-18c9-4ec5-9ebb-3bee71379d22

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
    ∑ j ∈ (allTagsExponent κ).support, allTagsExponent κ j = Fintype.card κ := by
  classical
  simp
end LatinQuarter
