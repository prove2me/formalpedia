-- Prove2me | solution 1 for Nock.Noun.cons_children_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:32:37.317509+00:00
-- url     : https://prove2.me/submissions/eecb3e82-a2a2-440b-b598-01945a4ff7a8

module
public import Definitions.Def_LeanPool_PureNock_Tree
public import Mathlib.Data.Multiset.Basic
public import Mathlib.Data.Multiset.AddSub
public import Mathlib.Data.Multiset.MapFold
public import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
public import Mathlib.Algebra.Ring.Nat
public import Definitions.Def_LeanPool_PureNock_NounValidation

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Noun
namespace Nock.Noun
theorem _root_.solution {l r l' r' : Noun} (h : Noun.cell l r = Noun.cell l' r') :
    l = l' ∧ r = r' := by
  injection h with h₁ h₂; exact ⟨h₁, h₂⟩
end Nock.Noun
