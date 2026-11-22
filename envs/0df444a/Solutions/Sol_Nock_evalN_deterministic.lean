-- Prove2me | solution 1 for Nock.evalN_deterministic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:20:00.762073+00:00
-- url     : https://prove2.me/submissions/e442a7ab-9e6b-4ecd-95be-145d1e788cf8

module
public import Definitions.Def_LeanPool_PureNock_Reference
public import Definitions.Def_LeanPool_PureNock_Semantics
public import Theorems.Thm_Nock_evalN_mono

set_option autoImplicit true
@[expose] public section
public section
open Nock
namespace Nock
theorem _root_.solution {n m : Nat} {s form r₁ r₂ : Noun}
    (h₁ : evalN n s form = some r₁) (h₂ : evalN m s form = some r₂) : r₁ = r₂ :=
  Option.some.inj ((evalN_mono (Nat.le_max_left n m) h₁).symm.trans
    (evalN_mono (Nat.le_max_right n m) h₂))
end Nock
