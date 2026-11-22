-- Prove2me | solution 1 for LatinQuarter.allTagsExponent_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:21:58.087756+00:00
-- url     : https://prove2.me/submissions/0e96eb92-1b2d-4790-8b26-52a206050016

module
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Definitions.Def_LeanPool_LatinQuarter_Tags
public import Theorems.Thm_LatinQuarter_tag_sq
public import Theorems.Thm_LatinQuarter_allTagsExponent_apply
attribute [local simp] LatinQuarter.tag_sq
attribute [local simp] LatinQuarter.allTagsExponent_apply

set_option autoImplicit true
@[expose] public section
public section
open LatinQuarter
open scoped BigOperators
open MvPolynomial
namespace LatinQuarter
theorem _root_.solution {κ : Type*} [Fintype κ] :
    (allTagsExponent κ).support = Finset.univ := by
  classical
  ext j
  simp
end LatinQuarter
