-- Prove2me | solution 1 for MatchingLogic.Pattern.freshTuple_not_mem_body_FV
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:37:11.932337+00:00
-- url     : https://prove2.me/submissions/717161b2-762d-4aa3-8c75-17d02da0539c

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CanonicalCore
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_MCSAlpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CanonicalExistence
public import Theorems.Thm_MatchingLogic_Pattern_freshTuple_not_mem_body_allVars
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
theorem _root_.solution (p : Pattern S Nat) (Phi : Fin n → Pattern S Nat)
    (i : Fin n) : freshTuple p Phi i ∉ FV p := by
  intro hi
  exact freshTuple_not_mem_body_allVars p Phi i (p.FV_subset_allVars hi)
end MatchingLogic.Pattern
