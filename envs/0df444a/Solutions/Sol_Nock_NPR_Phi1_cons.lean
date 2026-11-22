-- Prove2me | solution 1 for Nock.NPR.Phi1_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:30:05.266507+00:00
-- url     : https://prove2.me/submissions/da7fa4a4-0242-4385-bc5f-c089aa350e24

module
public import Definitions.Def_LeanPool_PureNock_Dyck
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Data.List.GetD
public import Mathlib.Tactic.FieldSimp
public import Definitions.Def_LeanPool_PureNock_NPR
public import Theorems.Thm_Nock_NPR_listPoly_nil
public import Theorems.Thm_Nock_NPR_leafF_length
public import Theorems.Thm_P2M_Nock_NPR___fst_7ffdc8e8ea0e
public import Theorems.Thm_P2M_Nock_NPR___snd_fst_ac932a0e2667
public import Theorems.Thm_P2M_Nock_NPR___snd_snd_5ccfc40ae445
public import Theorems.Thm_Nock_NPR_leafF_cell
attribute [local simp] Nock.NPR.listPoly_nil
attribute [local simp] Nock.NPR.leafF_length
attribute [local simp] Nock.NPR.Φ_fst
attribute [local simp] Nock.NPR.Φ_snd_fst
attribute [local simp] Nock.NPR.Φ_snd_snd
attribute [local simp] Nock.NPR.leafF_cell

set_option autoImplicit true
@[expose] public section
public section
open Polynomial
open Nock
open Nock.NPR
variable {K : Type*} [Field K]
namespace Nock.NPR
theorem _root_.solution (l r : Noun) :
    (Φ (K := K) (Noun.cell l r)).1 = (Φ l).1 * (Φ r).1 := by
  simp only [Φ_fst, Noun.leaves, pow_add]
end Nock.NPR
