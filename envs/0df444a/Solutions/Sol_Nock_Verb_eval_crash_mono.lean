-- Prove2me | solution 1 for Nock.Verb.eval_crash_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:19:19.541409+00:00
-- url     : https://prove2.me/submissions/cf888272-7b49-455b-94aa-f8d4a134675f

module
public import Definitions.Def_LeanPool_PureNock_Tree
public import Definitions.Def_LeanPool_PureNock_Reference
public import Definitions.Def_LeanPool_PureNock_Verb
public import Theorems.Thm_Nock_Verb_eval_succ

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
namespace Nock.Verb
theorem _root_.solution {n : Nat} {v : Verb} (h : eval n v = .crash) :
    eval (n + 1) v = .crash := by
  induction n generalizing v with
  | zero => simp [eval] at h
  | succ n ih =>
      rw [eval_succ] at h ⊢
      cases hnv : next v with
      | some v' => simp only [hnv] at h; exact ih h
      | none    => simp only [hnv] at h; exact h
end Nock.Verb
