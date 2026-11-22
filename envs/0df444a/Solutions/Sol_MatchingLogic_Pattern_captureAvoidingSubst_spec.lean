-- Prove2me | solution 1 for MatchingLogic.Pattern.captureAvoidingSubst_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:29:05.83906+00:00
-- url     : https://prove2.me/submissions/c500598a-976a-42a7-9c4f-1f69288cd23f

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Fresh
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Alpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_LocalTheory
public import Definitions.Def_LeanPool_MatchingLogic_Soundness
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CaptureAvoiding
public import Theorems.Thm_MatchingLogic_Pattern_avoidBinder_avoids
public import Theorems.Thm_MatchingLogic_Pattern_AvoidsBinder_captureFree
public import Theorems.Thm_MatchingLogic_Pattern_avoidBinder_alphaEq

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature}
open MatchingLogic.Pattern
open scoped BigOperators
namespace MatchingLogic.Pattern
theorem _root_.solution (x y : Nat) (p : Pattern S Nat) :
    IsCaptureAvoidingSubst x y p (captureAvoidingSubst x y p) := by
  refine ⟨avoidBinder y p, avoidBinder_alphaEq y p, ?_, rfl⟩
  exact (avoidBinder_avoids y p).captureFree
end MatchingLogic.Pattern
