-- Prove2me | solution 1 for MatchingLogic.Pattern.captureFree_rename_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:23:04.519719+00:00
-- url     : https://prove2.me/submissions/a1a863ce-2971-465b-8bd2-4f1ab877d140

module
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Mathlib.Logic.Denumerable
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Renaming
public import Theorems.Thm_MatchingLogic_Pattern_mem_FV_rename_injective

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var Var' Var'' : Type}
open MatchingLogic.Pattern
namespace MatchingLogic.Pattern
theorem _root_.solution
    (f : Var → Var') (hf : Function.Injective f) {x y : Var} {p : Pattern S Var}
    (h : CaptureFree x y p) :
    CaptureFree (f x) (f y) (p.rename f) := by
  classical
  induction p generalizing x y with
  | var z => trivial
  | bot => trivial
  | app sigma args ih =>
      intro i
      exact ih i (h i)
  | imp phi psi ihphi ihpsi =>
      exact ⟨ihphi h.1, ihpsi h.2⟩
  | ex z phi ih =>
      rcases h with hzx | hfree | ⟨hzy, hrec⟩
      · exact Or.inl (congrArg f hzx)
      · apply Or.inr (Or.inl ?_)
        intro hmem
        exact hfree ((mem_FV_rename_injective f hf phi x).mp hmem)
      · exact Or.inr (Or.inr ⟨fun heq => hzy (hf heq), ih hrec⟩)
end MatchingLogic.Pattern
