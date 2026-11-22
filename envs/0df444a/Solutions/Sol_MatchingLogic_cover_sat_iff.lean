-- Prove2me | solution 1 for MatchingLogic.cover_sat_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:29:10.052315+00:00
-- url     : https://prove2.me/submissions/d53a2262-827c-4644-8fa7-987996115499

module
public import Definitions.Def_LeanPool_MatchingLogic_DoubleCover
public import Definitions.Def_LeanPool_MatchingLogic_Localization
public import Definitions.Def_LeanPool_MatchingLogic_Locality
public import Definitions.Def_LeanPool_MatchingLogic_Composite
public import Theorems.Thm_MatchingLogic_cover_denote_closed

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]
variable (M : Model S) (C : Set M.carrier)
namespace MatchingLogic
theorem _root_.solution (hC : M.BackwardClosed C) (hne : C.Nonempty)
    (star : M.carrier) (hstar : star ∉ C)
    {ψ : Pattern S Var} (hψ : Closed ψ) (ρ : Var → M.carrier) :
    (cover M C hne).Sat ψ ↔ C ⊆ M.denote ρ ψ := by
  constructor
  · intro h q hq
    let p : C × Bool := (⟨q, hq⟩, false)
    let ν : Var → (C × Bool) := fun _ => p
    apply (cover_denote_closed M C hC hne star hstar hψ ν ρ p).mp
    have htotal := h ν
    rw [htotal]
    exact Set.mem_univ p
  · intro h ν
    apply Set.eq_univ_iff_forall.mpr
    intro p
    apply (cover_denote_closed M C hC hne star hstar hψ ν ρ p).mpr
    exact h p.1.property
end MatchingLogic
