-- Prove2me | solution 1 for LatinQuarter.tag_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:20:39.111957+00:00
-- url     : https://prove2.me/submissions/7b693ec3-c4e4-4f42-bead-9d3d913887e0

module
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Definitions.Def_LeanPool_LatinQuarter_Tags

set_option autoImplicit true
@[expose] public section
public section
open LatinQuarter
open scoped BigOperators
open MvPolynomial
namespace LatinQuarter
theorem _root_.solution {κ : Type*} (j : κ) : tag j * tag j = 0 := by
  rw [tag, ← map_mul]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply Ideal.subset_span
  refine ⟨Finsupp.single j 2, ⟨j, rfl⟩, ?_⟩
  simp [X, monomial_mul, ← Finsupp.single_add]
end LatinQuarter
