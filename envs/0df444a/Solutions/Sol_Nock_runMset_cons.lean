-- Prove2me | solution 1 for Nock.runMset_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:27:41.474282+00:00
-- url     : https://prove2.me/submissions/7f37a4c1-4cb9-401a-b362-2b59d86dcd91

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
namespace Nock
theorem _root_.solution {m m' : Multiset Noun} {n : Noun} {ch : Option (Noun × Noun)}
    {ts : Transcript} (h : stepMset m n ch = some m') :
    runMset m ((n, ch) :: ts) = runMset m' ts := by
  simp only [runMset, h]
end Nock
