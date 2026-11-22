-- Prove2me | solution 1 for MatchingLogic.closed_of_mem_localize
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:35:28.779115+00:00
-- url     : https://prove2.me/submissions/aa0fcef5-e778-4be5-9fd5-4238411dc96e

module
public import Definitions.Def_LeanPool_MatchingLogic_Boxes
public import Mathlib.Data.Set.Basic
public import Definitions.Def_LeanPool_MatchingLogic_Localization
public import Theorems.Thm_MatchingLogic_closed_boxes


set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]
omit [DecidableEq Var]
namespace MatchingLogic
theorem _root_.solution {Γ : Set (Pattern S Var)}
    (hΓ : ∀ γ ∈ Γ, Closed γ) : ∀ ψ ∈ localize Γ, Closed ψ := by
  rintro ψ ⟨γ, hγ, p, rfl⟩
  exact (closed_boxes p γ).2 (hΓ γ hγ)
end MatchingLogic
