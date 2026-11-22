-- Prove2me | solution 1 for Nock.evalPaperMod_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:28:39.694805+00:00
-- url     : https://prove2.me/submissions/6b10ca28-5ffb-4832-a73d-fdf06d00b89d

module
public import Definitions.Def_LeanPool_PureNock_PaperReference
public import Definitions.Def_LeanPool_PureNock_ModularEval
public import Definitions.Def_LeanPool_PureNock_PaperReferenceMod
public import Theorems.Thm_Nock_evalPaperMod_succ

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Noun
namespace Nock
theorem _root_.solution {q n m : Nat} {s form r : Noun}
    (hle : n ≤ m) (h : evalPaperMod q n s form = some r) : evalPaperMod q m s form = some r := by
  induction hle with
  | refl => exact h
  | step _ ih => exact evalPaperMod_succ ih
end Nock
