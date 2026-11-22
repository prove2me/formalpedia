-- Prove2me | solution 1 for MatchingLogic.generatedModel_interp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:26:30.529426+00:00
-- url     : https://prove2.me/submissions/c655b730-a32c-4d10-bf48-3c424673dd08

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
theorem _root_.solution (root : CanonicalCarrier S)
    (sigma : S.Sym)
    (components : Fin (S.arity sigma) → GeneratedCarrier root) :
    (generatedModel root).interp sigma components =
      generatedInterp root sigma components :=
  rfl
end MatchingLogic
