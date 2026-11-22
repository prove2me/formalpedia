-- Prove2me | solution 1 for MatchingLogic.mem_completedModel_interp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:39:03.898804+00:00
-- url     : https://prove2.me/submissions/b5eeadb7-0a0d-48f8-8a21-580ce2fda96f

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
theorem _root_.solution {root : CanonicalCarrier S}
    {sigma : S.Sym} {inputs : Fin (S.arity sigma) → CompletedCarrier root}
    {output : CompletedCarrier root} :
    output ∈ (completedModel root).interp sigma inputs ↔
      output ∈ completedInterp root sigma inputs :=
  Iff.rfl
end MatchingLogic
