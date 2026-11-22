-- Prove2me | solution 1 for LatinQuarter.allTagsExponent_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:21:17.476867+00:00
-- url     : https://prove2.me/submissions/169dc12e-195c-4a3c-9e05-7fd3ad58a976

module
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Definitions.Def_LeanPool_LatinQuarter_Tags
public import Theorems.Thm_LatinQuarter_tag_sq
attribute [local simp] LatinQuarter.tag_sq

set_option autoImplicit true
@[expose] public section
public section
open LatinQuarter
open scoped BigOperators
open MvPolynomial
namespace LatinQuarter
theorem _root_.solution {κ : Type*} [Fintype κ] (j : κ) :
    allTagsExponent κ j = 1 := by
  classical
  simp [allTagsExponent, Finsupp.single_apply]
end LatinQuarter
