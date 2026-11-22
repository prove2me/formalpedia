-- Prove2me | solution 1 for MatchingLogic.mem_canonicalInterp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:25:43.238812+00:00
-- url     : https://prove2.me/submissions/3aee6fa4-a90d-4471-bce7-e9ec2cd8e0e5

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
theorem _root_.solution {sigma : S.Sym}
    {components : Fin (S.arity sigma) → CanonicalCarrier S}
    {Gamma : CanonicalCarrier S} :
    Gamma ∈ canonicalInterp sigma components ↔
      ∀ args : Fin (S.arity sigma) → Pattern S Nat,
        (∀ i, args i ∈ (components i).val) →
          Pattern.app sigma args ∈ Gamma.val :=
  Iff.rfl
end MatchingLogic
