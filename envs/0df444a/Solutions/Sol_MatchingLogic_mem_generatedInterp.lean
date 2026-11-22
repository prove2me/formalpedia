-- Prove2me | solution 1 for MatchingLogic.mem_generatedInterp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:26:26.781316+00:00
-- url     : https://prove2.me/submissions/4115f2bc-d000-4f86-9606-63b5a5bbc957

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CanonicalCore
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_MCSAlpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Generated

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open Set
variable {S : Signature}
noncomputable section
attribute [local instance] MatchingLogic.instDecidableEqPatternNatGenerated
namespace MatchingLogic
theorem _root_.solution {root : CanonicalCarrier S} {sigma : S.Sym}
    {components : Fin (S.arity sigma) → GeneratedCarrier root}
    {world : GeneratedCarrier root} :
    world ∈ generatedInterp root sigma components ↔
      world.val ∈ canonicalInterp sigma (fun i => (components i).val) :=
  Iff.rfl
end MatchingLogic
