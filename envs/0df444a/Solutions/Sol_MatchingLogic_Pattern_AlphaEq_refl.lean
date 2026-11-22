-- Prove2me | solution 1 for MatchingLogic.Pattern.AlphaEq.refl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:24:09.683227+00:00
-- url     : https://prove2.me/submissions/a7960282-8e57-4e87-afde-c15e457d4e9f

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Fresh
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Alpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_LocalTheory
public import Definitions.Def_LeanPool_MatchingLogic_Soundness
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CaptureAvoiding
public import Theorems.Thm_MatchingLogic_Provable_imp_refl


set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature}
open MatchingLogic.Pattern
open scoped BigOperators
open MatchingLogic.Pattern.AlphaEq
namespace MatchingLogic.Pattern.AlphaEq
theorem _root_.solution (p : Pattern S Nat) : AlphaEq p p :=
  ⟨fun Gamma => .imp_refl Gamma p, fun Gamma => .imp_refl Gamma p, rfl⟩
end MatchingLogic.Pattern.AlphaEq
