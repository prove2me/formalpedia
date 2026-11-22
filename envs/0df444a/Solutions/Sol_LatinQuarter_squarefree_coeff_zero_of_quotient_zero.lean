-- Prove2me | solution 1 for LatinQuarter.squarefree_coeff_zero_of_quotient_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:20:46.493826+00:00
-- url     : https://prove2.me/submissions/7c435e95-aae7-40ea-8209-21a16cf96745

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
theorem _root_.solution {κ : Type*}
    {p : MvPolynomial κ (ZMod 2)}
    (hp : Ideal.Quotient.mk (repeatedTagIdeal κ) p = 0)
    {d : κ →₀ ℕ} (hd : ∀ j, d j ≤ 1) : p.coeff d = 0 :=
  squarefree_coeff_zero_of_mem (Ideal.Quotient.eq_zero_iff_mem.mp hp) hd
end LatinQuarter
