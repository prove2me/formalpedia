-- Prove2me | solution 1 for MatchingLogic.Necessity.locality_needs_backwardClosed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:35:23.726935+00:00
-- url     : https://prove2.me/submissions/b32746e9-4b47-4dd1-9ffe-ed082765b979

module
public import Definitions.Def_LeanPool_MatchingLogic_Locality
public import Mathlib.Data.Set.Insert
public import Definitions.Def_LeanPool_MatchingLogic_Necessity
public import Theorems.Thm_MatchingLogic_Necessity_agree
public import Theorems.Thm_MatchingLogic_Necessity_denote_rho
public import Theorems.Thm_P2M_MatchingLogic_Necessity_denote_rho__394e8edd322f

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open MatchingLogic.Necessity
variable {Var : Type} [DecidableEq Var]
namespace MatchingLogic.Necessity
theorem _root_.solution (x : Var) :
    ¬ (∀ (ψ : Pattern S Var) (ρ ρ' : Var → Fin 3),
        AgreeOn (M := M) C ρ ρ' → M.denote ρ ψ ∩ C = M.denote ρ' ψ ∩ C) := by
  intro h
  have hd := h (psi x) rho rho' agree
  rw [denote_rho, denote_rho'] at hd
  have h0 : (0 : Fin 3) ∈ ({0} : Set (Fin 3)) ∩ C := ⟨rfl, rfl⟩
  rw [hd] at h0
  exact h0.1
end MatchingLogic.Necessity
