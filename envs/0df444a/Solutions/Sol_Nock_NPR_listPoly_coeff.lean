-- Prove2me | solution 1 for Nock.NPR.listPoly_coeff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:29:53.877522+00:00
-- url     : https://prove2.me/submissions/6ceacfd9-9b2c-4666-a0cd-c4780efe0b90

module
public import Definitions.Def_LeanPool_PureNock_Dyck
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Data.List.GetD
public import Mathlib.Tactic.FieldSimp
public import Definitions.Def_LeanPool_PureNock_NPR
public import Theorems.Thm_Nock_NPR_cpoly_coeff

set_option autoImplicit true
@[expose] public section
public section
open Polynomial
open Nock
open Nock.NPR
variable {K : Type*} [Field K]
namespace Nock.NPR
theorem _root_.solution (l : List K) (j : ℕ) :
    (listPoly l).coeff j = if j < l.length then l.getD j 0 else 0 := by
  unfold listPoly; rw [cpoly_coeff]
end Nock.NPR
