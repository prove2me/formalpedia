-- Prove2me | solution 1 for MatchingLogic.Necessity.locality_needs_backwardClosed_nat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:45:48.157818+00:00
-- url     : https://prove2.me/submissions/319d2a4a-e0a1-498c-b68b-124dfc9fb9ee

module
public import Definitions.Def_LeanPool_MatchingLogic_Locality
public import Mathlib.Data.Set.Insert
public import Definitions.Def_LeanPool_MatchingLogic_Necessity
public import Theorems.Thm_MatchingLogic_Necessity_locality_needs_backwardClosed

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open MatchingLogic.Necessity
namespace MatchingLogic.Necessity
theorem _root_.solution :
    ¬ (∀ (ψ : Pattern S Nat) (ρ ρ' : Nat → Fin 3),
        AgreeOn (M := M) C ρ ρ' → M.denote ρ ψ ∩ C = M.denote ρ' ψ ∩ C) :=
  locality_needs_backwardClosed 0
end MatchingLogic.Necessity
