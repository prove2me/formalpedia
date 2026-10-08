-- Prove2me | solution 1 for OAI.PiExponent.derivation_basis_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-07T07:27:39.255656+00:00
-- url     : https://prove2.me/submissions/05250fcc-4dbb-4a54-946d-ea03fee70ed2

import Mathlib.Algebra.Polynomial.Derivation
import Mathlib.Algebra.Polynomial.Div
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.Trace.Defs
import Mathlib.Tactic

import Theorems.Thm_OAI_PiExponent_derivation_intermediate_smul
namespace OAI
namespace PiExponent
end PiExponent
end OAI
open scoped LaurentSeries Matrix
open Polynomial
open OAI.PiExponent

theorem solution
    {k F E ι : Type*} [Field k] [Field F] [Field E] [Fintype ι]
    [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
    (d : Derivation k F F) (D : Derivation k E E)
    (hcompat : ∀ a : F, D (algebraMap F E a) = algebraMap F E (d a))
    (b : Module.Basis ι F E) (z : E) (i : ι) :
    b.repr (D z) i = d (b.repr z i) +
      ∑ j, b.repr z j * b.repr (D (b j)) i := by
  classical
  conv_lhs => rw [← b.sum_repr z]
  simp only [map_sum, derivation_intermediate_smul d D hcompat, map_add,
    map_smul, Finset.sum_add_distrib, Finsupp.coe_add, Pi.add_apply,
    Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
  simp [Finsupp.single_apply, eq_comm]
