-- Prove2me | solution 1 for MatchingLogic.canonicalModel_interp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:25:43.77549+00:00
-- url     : https://prove2.me/submissions/6ee12e36-fe21-4f85-be6c-6a161078befb

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Witnessed
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_MCSAlpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CanonicalCore

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open Set
variable {S : Signature}
noncomputable section
attribute [local instance] MatchingLogic.instDecidableEqPatternNatCanonicalCore
namespace MatchingLogic
theorem _root_.solution (root : CanonicalCarrier S)
    (sigma : S.Sym) (components : Fin (S.arity sigma) → CanonicalCarrier S) :
    (canonicalModel root).interp sigma components = canonicalInterp sigma components :=
  rfl
end MatchingLogic
