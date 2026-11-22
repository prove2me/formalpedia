-- Prove2me | solution 1 for MatchingLogic.Pattern.freshTuple_not_mem_component_FV
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:37:13.008703+00:00
-- url     : https://prove2.me/submissions/c053909f-697e-4f93-b607-660525e12ffb

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CanonicalCore
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_MCSAlpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CanonicalExistence
public import Theorems.Thm_MatchingLogic_Pattern_freshTuple_not_mem_component_allVars
public import Theorems.Thm_MatchingLogic_Pattern_FV_subset_allVars


set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open Set
variable {S : Signature}
noncomputable section
open MatchingLogic.Pattern
namespace MatchingLogic.Pattern
theorem _root_.solution (p : Pattern S Nat)
    (Phi : Fin n → Pattern S Nat) (i j : Fin n) : freshTuple p Phi i ∉ FV (Phi j) := by
  intro hi
  exact freshTuple_not_mem_component_allVars p Phi i j ((Phi j).FV_subset_allVars hi)
end MatchingLogic.Pattern
