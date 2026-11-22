-- Prove2me | solution 1 for Nock.Verb.vcostN_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:26:41.89032+00:00
-- url     : https://prove2.me/submissions/7ba52ca9-7150-4b18-98da-1a9427516651

module
public import Definitions.Def_LeanPool_PureNock_PureComplete
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureCompleteHint
public import Theorems.Thm_Nock_Verb_den_children_F
public import Theorems.Thm_Nock_Verb_ncost_succ
public import Theorems.Thm_Nock_Verb_den_succ
public import Theorems.Thm_Nock_Verb_editOk_children
public import Theorems.Thm_Nock_evalN_succ


set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {F : Nat} {v : Verb} {x : Noun}
    (hok : editOk v = true) (hv : den F v = some x) : vcostN (F + 1) v = vcostN F v := by
  induction v generalizing F x with
  | leaf k => rfl
  | node a l r ihl ihr =>
      obtain ⟨f, rfl⟩ : ∃ f, F = f + 1 := by
        cases F with
        | zero => simp [den] at hv
        | succ n => exact ⟨n, rfl⟩
      obtain ⟨hokl, hokr⟩ := editOk_children hok
      obtain ⟨⟨yl, hyl⟩, ⟨yr, hyr⟩⟩ := den_children_F hok hv
      have ihl' : vcostN (f + 1 + 1) l = vcostN (f + 1) l := ihl hokl hyl
      have ihr' : vcostN (f + 1 + 1) r = vcostN (f + 1) r := ihr hokr hyr
      cases a with
      | null => simp only [vcostN, ihl', ihr']
      | wut => simp [den] at hv
      | slot => simp only [vcostN, ihl', ihr']
      | equal => simp only [vcostN, ihl', ihr']
      | minus => simp only [vcostN, ihl', ihr']
      | edit => simp only [vcostN, ihl', ihr']
      | star =>
          simp only [den] at hv
          cases hfl : den f l with
          | none => rw [hfl] at hv; simp at hv
          | some sa =>
              cases hfr : den f r with
              | none => rw [hfl, hfr] at hv; simp at hv
              | some fo =>
                  rw [hfl, hfr] at hv
                  have hdl1 : den (f + 1) l = some sa := den_succ hfl
                  have hdr1 : den (f + 1) r = some fo := den_succ hfr
                  have hdl2 : den (f + 1 + 1) l = some sa := den_succ hdl1
                  have hdr2 : den (f + 1 + 1) r = some fo := den_succ hdr1
                  have hev1 : evalN (f + 1) sa fo = some x := evalN_succ hv
                  have hpc : ncost (f + 1 + 1) sa fo = ncost (f + 1) sa fo := ncost_succ hev1
                  simp only [vcostN, hdl1, hdr1, hdl2, hdr2, hpc, ihl', ihr']
end Nock.Verb
