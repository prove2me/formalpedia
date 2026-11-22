-- Prove2me | solution 1 for Nock.NPR.listPoly_sub_natDegree_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:30:52.591386+00:00
-- url     : https://prove2.me/submissions/9587d6f7-516e-41e1-8297-4ff84b69339c

module
public import Definitions.Def_LeanPool_PureNock_Dyck
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Data.List.GetD
public import Mathlib.Tactic.FieldSimp
public import Definitions.Def_LeanPool_PureNock_NPR
public import Theorems.Thm_Nock_NPR_listPoly_natDegree_le

set_option autoImplicit true
@[expose] public section
public section
open Polynomial
open Nock
open Nock.NPR
variable {K : Type*} [Field K]
namespace Nock.NPR
theorem _root_.solution {l₁ l₂ : List K} (hlen : l₁.length = l₂.length) :
    (listPoly l₁ - listPoly l₂).natDegree ≤ l₁.length - 1 := by
  refine le_trans (natDegree_sub_le _ _) ?_
  rw [max_le_iff]
  exact ⟨listPoly_natDegree_le l₁, by rw [hlen]; exact listPoly_natDegree_le l₂⟩
end Nock.NPR
