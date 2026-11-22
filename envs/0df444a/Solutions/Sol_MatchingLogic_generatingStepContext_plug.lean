-- Prove2me | solution 1 for MatchingLogic.generatingStepContext_plug
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:26:40.837304+00:00
-- url     : https://prove2.me/submissions/598469ee-170d-4e9d-af42-ec457ef29925

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
theorem _root_.solution (e : Coord S) (p : Pattern S Nat) :
    (generatingStepContext e).plug p =
      .app e.1 (Function.update (fun _ => Pattern.tp) e.2 p) :=
  rfl
end MatchingLogic
