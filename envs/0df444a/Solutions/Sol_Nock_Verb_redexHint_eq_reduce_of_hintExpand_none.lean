-- Prove2me | solution 1 for Nock.Verb.redexHint_eq_reduce_of_hintExpand_none
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:25:14.424946+00:00
-- url     : https://prove2.me/submissions/32784a5a-c367-422d-8fab-bb1d818be487

module
public import Definitions.Def_LeanPool_PureNock_PureComplete
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureCompleteHint

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {v : Verb} (h : hintExpand v = none) :
    redexHint v = reduce v := by
  unfold redexHint; rw [h]
end Nock.Verb
