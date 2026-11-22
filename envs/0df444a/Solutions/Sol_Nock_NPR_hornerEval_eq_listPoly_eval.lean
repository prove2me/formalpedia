-- Prove2me | solution 1 for Nock.NPR.hornerEval_eq_listPoly_eval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:30:56.269413+00:00
-- url     : https://prove2.me/submissions/0ebcd56a-03f0-4bbf-8b56-677c6d1e026c

module
public import Definitions.Def_LeanPool_PureNock_NPR
public import Definitions.Def_LeanPool_PureNock_Fingerprint
public import Theorems.Thm_Nock_NPR_leafF_cell
public import Theorems.Thm_Nock_NPR_leafF_length
public import Theorems.Thm_Nock_NPR_listPoly_cons
public import Theorems.Thm_Nock_NPR_listPoly_nil
public import Theorems.Thm_P2M_Nock_NPR___fst_7ffdc8e8ea0e
public import Theorems.Thm_P2M_Nock_NPR___snd_fst_ac932a0e2667
public import Theorems.Thm_P2M_Nock_NPR___snd_snd_5ccfc40ae445
attribute [local simp] Nock.NPR.leafF_cell
attribute [local simp] Nock.NPR.leafF_length
attribute [local simp] Nock.NPR.listPoly_nil
attribute [local simp] P2M_Nock_NPR___fst_7ffdc8e8ea0e
attribute [local simp] P2M_Nock_NPR___snd_fst_ac932a0e2667
attribute [local simp] P2M_Nock_NPR___snd_snd_5ccfc40ae445



set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.NPR
open Polynomial
variable {K : Type*} [Field K]
namespace Nock.NPR
theorem _root_.solution (r : K) (l : List K) :
    hornerEval r l = (listPoly l).eval r := by
  induction l with
  | nil => simp [hornerEval, listPoly_nil]
  | cons x l ih =>
      simp only [hornerEval, listPoly_cons, eval_add, eval_C, eval_mul, eval_X, ih]
end Nock.NPR
