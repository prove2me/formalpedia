-- Prove2me | solution 1 for Nock.evalPaperMod_deterministic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:33:28.847915+00:00
-- url     : https://prove2.me/submissions/932f1860-5dbd-42a3-bda9-8e943d00d9c9

module
public import Definitions.Def_LeanPool_PureNock_PureCompleteHint
public import Definitions.Def_LeanPool_PureNock_PaperReferenceMod
public import Definitions.Def_LeanPool_PureNock_Determinism
public import Theorems.Thm_Nock_evalPaperMod_mono


set_option autoImplicit true
@[expose] public section
public section
open Nock
namespace Nock
theorem _root_.solution {q n m : Nat} {s form r₁ r₂ : Noun}
    (h₁ : evalPaperMod q n s form = some r₁) (h₂ : evalPaperMod q m s form = some r₂) : r₁ = r₂ :=
  Option.some.inj ((evalPaperMod_mono (Nat.le_max_left n m) h₁).symm.trans
    (evalPaperMod_mono (Nat.le_max_right n m) h₂))
end Nock
