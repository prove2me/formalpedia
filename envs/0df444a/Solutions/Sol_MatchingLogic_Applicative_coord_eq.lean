-- Prove2me | solution 1 for MatchingLogic.Applicative.coord_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:35:34.387896+00:00
-- url     : https://prove2.me/submissions/0e2989f5-bb5e-44e3-9816-982f3c73e005

module
public import Mathlib.Data.Fin.VecNotation
public import Definitions.Def_LeanPool_MatchingLogic_Localization
public import Definitions.Def_LeanPool_MatchingLogic_Composite
public import Definitions.Def_LeanPool_MatchingLogic_Applicative
section
@[expose] public section
namespace MatchingLogic
namespace Applicative
variable {Const : Type} {Var : Type} [DecidableEq Var]
private theorem fin_two_cases (i : Fin 2) : i = 0 ∨ i = 1 := by
  omega
end Applicative
end MatchingLogic
end
end

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open MatchingLogic.Applicative
variable {Const : Type} {Var : Type} [DecidableEq Var]
namespace MatchingLogic.Applicative
theorem _root_.solution (e : Coord (appSig Const)) : e = coord₁ ∨ e = coord₂ := by
  rcases e with ⟨s, i⟩
  cases s with
  | none =>
      change Fin 2 at i
      rcases fin_two_cases i with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
  | some c =>
      exact Fin.elim0 i
end MatchingLogic.Applicative
