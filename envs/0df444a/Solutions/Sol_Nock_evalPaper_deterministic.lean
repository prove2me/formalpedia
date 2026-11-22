-- Prove2me | solution 1 for Nock.evalPaper_deterministic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:20:03.808437+00:00
-- url     : https://prove2.me/submissions/08075d9f-eb09-41a7-abe5-1d98470cc5ea

module
public import Definitions.Def_LeanPool_PureNock_Reference
public import Definitions.Def_LeanPool_PureNock_PaperReference
public import Theorems.Thm_Nock_evalPaper_mono

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Noun
namespace Nock
theorem _root_.solution {n m : Nat} {s form r₁ r₂ : Noun}
    (h₁ : evalPaper n s form = some r₁) (h₂ : evalPaper m s form = some r₂) : r₁ = r₂ :=
  Option.some.inj ((evalPaper_mono (Nat.le_max_left n m) h₁).symm.trans
    (evalPaper_mono (Nat.le_max_right n m) h₂))
end Nock
