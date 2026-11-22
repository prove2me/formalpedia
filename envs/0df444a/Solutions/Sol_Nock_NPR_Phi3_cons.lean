-- Prove2me | solution 1 for Nock.NPR.Phi3_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:31:30.901804+00:00
-- url     : https://prove2.me/submissions/eb3560c6-d896-4b62-90a6-810cfe2fadfb

module
public import Definitions.Def_LeanPool_PureNock_Dyck
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Data.List.GetD
public import Mathlib.Tactic.FieldSimp
public import Definitions.Def_LeanPool_PureNock_NPR
public import Theorems.Thm_Nock_NPR_listPoly_nil
public import Theorems.Thm_Nock_NPR_listPoly_cons
public import Theorems.Thm_Nock_NPR_listPoly_append
public import Theorems.Thm_Nock_NPR_leafF_length
public import Theorems.Thm_Nock_NPR_dyckBits_length
public import Theorems.Thm_P2M_Nock_NPR___fst_7ffdc8e8ea0e
public import Theorems.Thm_P2M_Nock_NPR___snd_fst_ac932a0e2667
public import Theorems.Thm_P2M_Nock_NPR___snd_snd_5ccfc40ae445
public import Theorems.Thm_Nock_NPR_leafF_cell
public import Theorems.Thm_Nock_NPR_dyckBits_cell
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
    (Φ (K := K) (Noun.cell l r)).2.2
      = X * (Φ l).2.2 + X ^ (2 * l.leaves - 1) + X ^ (2 * l.leaves) * (Φ r).2.2 := by
  have hd : (dyckBits (K := K) l).length + 2 = 2 * l.leaves := dyckBits_length l
  have h1 : (dyckBits (K := K) l).length + 1 = 2 * l.leaves - 1 := by omega
  simp only [Φ_snd_snd, dyckBits_cell, listPoly_cons, listPoly_append, C_0, C_1]
  rw [← h1, ← hd]
  ring
end Nock.NPR
