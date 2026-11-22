-- Prove2me | solution 1 for Nock.NPR.leafF_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:00:49.03485+00:00
-- url     : https://prove2.me/submissions/ca482dce-b8b3-46ac-9ea5-8fc75b4d154d

module
public import Definitions.Def_LeanPool_PureNock_Dyck
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Data.List.GetD
public import Mathlib.Tactic.FieldSimp
public import Definitions.Def_LeanPool_PureNock_NPR
public import Theorems.Thm_Nock_NPR_listPoly_nil
attribute [local simp] Nock.NPR.listPoly_nil

set_option autoImplicit true
@[expose] public section
public section
open Polynomial
open Nock
open Nock.NPR
variable {K : Type*} [Field K]
namespace Nock.NPR
theorem _root_.solution (n : Noun) : (leafF (K := K) n).length = n.leaves := by
  simp [leafF]
end Nock.NPR
