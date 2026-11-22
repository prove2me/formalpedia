-- Prove2me | solution 1 for MatchingLogic.completedModel_interp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:29:18.674521+00:00
-- url     : https://prove2.me/submissions/b3e2a5a4-653d-4531-8079-4938d8c7eb40

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Generated
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Completion

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open Set
variable {S : Signature}
noncomputable section
attribute [local instance] MatchingLogic.instDecidableEqPatternNatCompletion
namespace MatchingLogic
theorem _root_.solution (root : CanonicalCarrier S)
    (sigma : S.Sym)
    (inputs : Fin (S.arity sigma) → CompletedCarrier root) :
    (completedModel root).interp sigma inputs = completedInterp root sigma inputs :=
  rfl
end MatchingLogic
