-- Prove2me | solution 1 for Nock.NPR.listPoly_natDegree_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:30:27.246185+00:00
-- url     : https://prove2.me/submissions/9191606c-d299-4367-a5d8-04a1f8a2a024

module
public import Definitions.Def_LeanPool_PureNock_Dyck
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Data.List.GetD
public import Mathlib.Tactic.FieldSimp
public import Definitions.Def_LeanPool_PureNock_NPR
public import Theorems.Thm_Nock_NPR_cpoly_natDegree_le

set_option autoImplicit true
@[expose] public section
public section
open Polynomial
open Nock
open Nock.NPR
variable {K : Type*} [Field K]
namespace Nock.NPR
theorem _root_.solution (l : List K) : (listPoly l).natDegree ≤ l.length - 1 :=
  cpoly_natDegree_le _ _
end Nock.NPR
