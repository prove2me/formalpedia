-- Prove2me | solution 1 for MatchingLogic.mem_canonicalModel_interp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:37:07.549073+00:00
-- url     : https://prove2.me/submissions/78bfb5a2-aa5d-4227-b138-6db01af57221

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
    {sigma : S.Sym} {components : Fin (S.arity sigma) → CanonicalCarrier S}
    {Gamma : CanonicalCarrier S} :
    Gamma ∈ (canonicalModel root).interp sigma components ↔
      ∀ args : Fin (S.arity sigma) → Pattern S Nat,
        (∀ i, args i ∈ (components i).val) →
          Pattern.app sigma args ∈ Gamma.val :=
  Iff.rfl
end MatchingLogic
