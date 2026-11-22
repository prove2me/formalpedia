-- Prove2me | solution 1 for MatchingLogic.mem_generatedModel_interp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:39:49.792963+00:00
-- url     : https://prove2.me/submissions/f3c6cf1e-195b-41dd-9534-87b5b64664c4

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
theorem _root_.solution {root : CanonicalCarrier S}
    {sigma : S.Sym} {components : Fin (S.arity sigma) → GeneratedCarrier root}
    {world : GeneratedCarrier root} :
    world ∈ (generatedModel root).interp sigma components ↔
      world.val ∈ canonicalInterp sigma (fun i => (components i).val) :=
  Iff.rfl
end MatchingLogic
