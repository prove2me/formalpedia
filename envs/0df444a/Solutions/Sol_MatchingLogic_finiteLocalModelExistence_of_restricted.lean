-- Prove2me | solution 1 for MatchingLogic.finiteLocalModelExistence_of_restricted
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:43:00.06825+00:00
-- url     : https://prove2.me/submissions/5f5b5d21-2402-4ebb-9ded-beaa935d9170

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Countertheory
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_SignatureRestriction
public import Mathlib.Tactic.Bound.Init
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_SignatureReduction
public import Theorems.Thm_MatchingLogic_Pattern_symbolSupport_subset_symbolSupportList
public import Theorems.Thm_MatchingLogic_Pattern_liftSignature_restrictList
public import Theorems.Thm_MatchingLogic_Model_denoteSet_extendSignature_liftSignature_list
public import Theorems.Thm_MatchingLogic_restrictList_locConsistent
public import Theorems.Thm_MatchingLogic_Provable_liftSignature


set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]
namespace MatchingLogic
theorem _root_.solution
    (hmodel : ∀ F : Finset S.Sym, FiniteLocalModelExistence (S.restrict F) Nat) :
    FiniteLocalModelExistence S Nat := by
  classical
  intro l hconsistent
  let F : Finset S.Sym := Pattern.symbolSupportList l
  have hsupport : ∀ p ∈ l, p.symbolSupport ⊆ F := by
    intro p hp
    exact Pattern.symbolSupport_subset_symbolSupportList l hp
  let restricted : List (Pattern (S.restrict F) Nat) :=
    Pattern.restrictList F l hsupport
  have hrestrictedConsistent : LocConsistent {delta | delta ∈ restricted} := by
    exact restrictList_locConsistent F l hsupport hconsistent
  obtain ⟨M, rho, u, hu⟩ := hmodel F restricted hrestrictedConsistent
  refine ⟨M.extendSignature F, rho, u, ?_⟩
  have huLifted : u ∈ (M.extendSignature F).denoteSet rho
      {delta | delta ∈ restricted.map (Pattern.liftSignature F)} := by
    rw [M.denoteSet_extendSignature_liftSignature_list]
    exact hu
  have hlift : restricted.map (Pattern.liftSignature F) = l := by
    exact Pattern.liftSignature_restrictList F l hsupport
  rwa [hlift] at huLifted
end MatchingLogic
