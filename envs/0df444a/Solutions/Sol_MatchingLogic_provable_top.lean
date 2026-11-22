-- Prove2me | solution 1 for MatchingLogic.provable_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:16:27.682418+00:00
-- url     : https://prove2.me/submissions/88ff69be-3407-4fb5-82dd-5f8d5ef0a6d3

module
public import Definitions.Def_LeanPool_MatchingLogic_Boxes
public import Mathlib.Data.Set.Insert
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
section
@[expose] public section
namespace MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]
private theorem taut_top : PForm.Taut (.imp .bot .bot) := by
  intro _
  rfl
end MatchingLogic
end
end

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]
namespace MatchingLogic
theorem _root_.solution (Γ : Set (Pattern S Var)) :
    Provable Γ (Pattern.tp : Pattern S Var) := by
  exact .taut (θ := fun _ => .bot) taut_top
end MatchingLogic
