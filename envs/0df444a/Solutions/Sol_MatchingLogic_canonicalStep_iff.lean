-- Prove2me | solution 1 for MatchingLogic.canonicalStep_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:26:37.794034+00:00
-- url     : https://prove2.me/submissions/246fae9a-7324-4cf8-807d-6915d681c4b1

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
theorem _root_.solution (parent child : CanonicalCarrier S) :
    canonicalStep parent child ↔
      ∃ (sigma : S.Sym)
        (components : Fin (S.arity sigma) → CanonicalCarrier S)
        (i : Fin (S.arity sigma)),
        parent ∈ canonicalInterp sigma components ∧ child = components i :=
  Iff.rfl
end MatchingLogic
