-- Prove2me | solution 1 for MatchingLogic.mem_completedInterp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:28:55.225091+00:00
-- url     : https://prove2.me/submissions/e71898cb-b64c-4116-ab3f-3111e9b21862

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
theorem _root_.solution {root : CanonicalCarrier S} {sigma : S.Sym}
    {inputs : Fin (S.arity sigma) → CompletedCarrier root}
    {output : CompletedCarrier root} :
    output ∈ completedInterp root sigma inputs ↔
      ∃ components : Fin (S.arity sigma) → GeneratedCarrier root,
        (∀ i, inputs i = completedEmbed root (components i)) ∧
          ((∃ world : GeneratedCarrier root,
              output = completedEmbed root world ∧
                world ∈ generatedInterp root sigma components) ∨
           (output.isStar ∧ ∃ i, components i = generatedRoot root)) :=
  Iff.rfl
end MatchingLogic
