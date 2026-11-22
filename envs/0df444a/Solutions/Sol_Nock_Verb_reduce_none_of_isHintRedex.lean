-- Prove2me | solution 1 for Nock.Verb.reduce_none_of_isHintRedex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:21:53.845659+00:00
-- url     : https://prove2.me/submissions/470e084d-6095-43cd-a2eb-9fd0591479f1

module
public import Definitions.Def_LeanPool_PureNock_Agreement
public import Definitions.Def_LeanPool_PureNock_Trace
public import Definitions.Def_LeanPool_PureNock_PaperReference
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureAgreement

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {sub} (h : isHintRedex sub = true) : reduce sub = none := by
  unfold isHintRedex at h
  split at h
  · rename_i n1 ra rn hh b
    simp [reduce, redex]
  · simp at h
end Nock.Verb
