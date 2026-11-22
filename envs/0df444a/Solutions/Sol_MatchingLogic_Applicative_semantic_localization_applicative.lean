-- Prove2me | solution 1 for MatchingLogic.Applicative.semantic_localization_applicative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:36:03.688185+00:00
-- url     : https://prove2.me/submissions/857434b3-7bbd-402d-9e7f-10518933ac97

module
public import Mathlib.Data.Fin.VecNotation
public import Definitions.Def_LeanPool_MatchingLogic_Localization
public import Definitions.Def_LeanPool_MatchingLogic_Composite
public import Definitions.Def_LeanPool_MatchingLogic_Applicative
public import Theorems.Thm_MatchingLogic_semantic_localization


set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open MatchingLogic.Applicative
variable {Const : Type} {Var : Type} [DecidableEq Var]
namespace MatchingLogic.Applicative
theorem _root_.solution
    {Γ : Set (Pattern (appSig Const) Var)} {φ : Pattern (appSig Const) Var}
    (hΓ : ∀ γ ∈ Γ, Closed γ) (hφ : Closed φ) :
    GlobalCons Γ φ ↔ LocalCons (localize Γ) φ := by
  exact semantic_localization hΓ hφ
end MatchingLogic.Applicative
