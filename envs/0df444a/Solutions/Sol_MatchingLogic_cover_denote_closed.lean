-- Prove2me | solution 1 for MatchingLogic.cover_denote_closed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:28:21.239566+00:00
-- url     : https://prove2.me/submissions/3fe0ad3b-edd6-4478-880a-2f780ed799b5

module
public import Definitions.Def_LeanPool_MatchingLogic_DoubleCover
public import Definitions.Def_LeanPool_MatchingLogic_Localization
public import Definitions.Def_LeanPool_MatchingLogic_Locality
public import Definitions.Def_LeanPool_MatchingLogic_Composite
public import Theorems.Thm_MatchingLogic_denote_closed
public import Theorems.Thm_MatchingLogic_two_copies


set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]
variable (M : Model S) (C : Set M.carrier)
namespace MatchingLogic
theorem _root_.solution (hC : M.BackwardClosed C) (hne : C.Nonempty)
    (star : M.carrier) (hstar : star ∉ C)
    {ψ : Pattern S Var} (hψ : Closed ψ)
    (ν : Var → (C × Bool)) (ρ : Var → M.carrier) (p : C × Bool) :
    p ∈ (cover M C hne).denote ν ψ ↔ (p.1 : M.carrier) ∈ M.denote ρ ψ := by
  rw [two_copies M C hC hne star hstar ψ ν p]
  rw [denote_closed M hψ (fun x => proj M C star p.2 (ν x)) ρ]
end MatchingLogic
