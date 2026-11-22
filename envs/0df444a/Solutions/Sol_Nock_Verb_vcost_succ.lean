-- Prove2me | solution 1 for Nock.Verb.vcost_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:24:31.025804+00:00
-- url     : https://prove2.me/submissions/9c627a94-9ac2-4985-9cba-8507caa9c517

module
public import Definitions.Def_LeanPool_PureNock_PureAgreement
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureComplete
public import Theorems.Thm_Nock_Verb_denP_children_F
public import Theorems.Thm_Nock_Verb_denP_succ
public import Theorems.Thm_Nock_Verb_editOk_children
public import Theorems.Thm_Nock_Verb_pcost_succ
public import Theorems.Thm_Nock_evalPaper_succ


set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {F : Nat} {v : Verb} {x : Noun}
    (hok : editOk v = true) (hv : denP F v = some x) : vcost (F + 1) v = vcost F v := by
  induction v generalizing F x with
  | leaf k => rfl
  | node a l r ihl ihr =>
      obtain ⟨f, rfl⟩ : ∃ f, F = f + 1 := by
        cases F with
        | zero => simp [denP] at hv
        | succ n => exact ⟨n, rfl⟩
      obtain ⟨hokl, hokr⟩ := editOk_children hok
      obtain ⟨⟨yl, hyl⟩, ⟨yr, hyr⟩⟩ := denP_children_F hok hv
      have ihl' : vcost (f + 1 + 1) l = vcost (f + 1) l := ihl hokl hyl
      have ihr' : vcost (f + 1 + 1) r = vcost (f + 1) r := ihr hokr hyr
      cases a with
      | null => simp only [vcost, ihl', ihr']
      | wut => simp [denP] at hv
      | slot => simp only [vcost, ihl', ihr']
      | equal => simp only [vcost, ihl', ihr']
      | minus => simp only [vcost, ihl', ihr']
      | edit => simp only [vcost, ihl', ihr']
      | star =>
          -- unfold star clause; both fuels pick the same denP values sa, fo
          simp only [denP] at hv
          -- hv : (match denP f l, denP f r with ...) = some x
          cases hfl : denP f l with
          | none => rw [hfl] at hv; simp at hv
          | some sa =>
              cases hfr : denP f r with
              | none => rw [hfl, hfr] at hv; simp at hv
              | some fo =>
                  rw [hfl, hfr] at hv
                  -- hv : evalPaper f sa fo = some x
                  have hdl1 : denP (f + 1) l = some sa := denP_succ hfl
                  have hdr1 : denP (f + 1) r = some fo := denP_succ hfr
                  have hdl2 : denP (f + 1 + 1) l = some sa := denP_succ hdl1
                  have hdr2 : denP (f + 1 + 1) r = some fo := denP_succ hdr1
                  have hev1 : evalPaper (f + 1) sa fo = some x := evalPaper_succ hv
                  have hpc : pcost (f + 1 + 1) sa fo = pcost (f + 1) sa fo := pcost_succ hev1
                  simp only [vcost, hdl1, hdr1, hdl2, hdr2, hpc, ihl', ihr']
end Nock.Verb
