-- Prove2me | solution 1 for MatchingLogic.Pattern.IsCaptureAvoidingSubst.exQuant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:24:32.611367+00:00
-- url     : https://prove2.me/submissions/0afdb937-3b67-4d05-81fa-535d8dc785d4

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Fresh
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Alpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_LocalTheory
public import Definitions.Def_LeanPool_MatchingLogic_Soundness
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CaptureAvoiding
public import Theorems.Thm_MatchingLogic_Provable_imp_trans


set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature}
namespace MatchingLogic
namespace Pattern.IsCaptureAvoidingSubst
theorem _root_.solution {Gamma : Set (Pattern S Nat)}
    {x y : Nat} {p q : Pattern S Nat} (h : IsCaptureAvoidingSubst x y p q) :
    Provable Gamma (.imp q (.ex x p)) := by
  rcases h with ⟨p', halpha, hcf, rfl⟩
  exact (Provable.exQuant hcf).imp_trans ((AlphaEq.ex x halpha).backward Gamma)
end Pattern.IsCaptureAvoidingSubst
end MatchingLogic
