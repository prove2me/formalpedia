-- Prove2me | solution 1 for Nock.NPR.fnHorner_eq_fn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:34:05.988715+00:00
-- url     : https://prove2.me/submissions/dddda8af-163f-4004-a7d0-41d0f84a29af

module
public import Definitions.Def_LeanPool_PureNock_NPR
public import Definitions.Def_LeanPool_PureNock_Fingerprint
public import Theorems.Thm_Nock_NPR_hornerEval_eq_listPoly_eval
public import Theorems.Thm_Nock_NPR_leafF_cell
public import Theorems.Thm_Nock_NPR_leafF_length
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
theorem _root_.solution (n : Noun) (r : K) : fnHorner r n = fn n r := by
  simp only [fnHorner, fn, hornerEval_eq_listPoly_eval]
end Nock.NPR
