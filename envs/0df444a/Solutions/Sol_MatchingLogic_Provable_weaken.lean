-- Prove2me | solution 1 for MatchingLogic.Provable.weaken
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:21:59.92004+00:00
-- url     : https://prove2.me/submissions/cdcd3b96-0b88-4e27-8ab5-020e6851f83f

module
public import Definitions.Def_LeanPool_MatchingLogic_Boxes
public import Mathlib.Data.Set.Insert
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]
namespace MatchingLogic
namespace Provable
theorem _root_.solution {Γ Δ : Set (Pattern S Var)} {φ : Pattern S Var}
    (hΓΔ : Γ ⊆ Δ) (h : Provable Γ φ) : Provable Δ φ := by
  induction h with
  | hyp hφ => exact .hyp (hΓΔ hφ)
  | taut hp => exact .taut hp
  | mp _ _ ihφ himp => exact .mp ihφ himp
  | exQuant hfree => exact .exQuant hfree
  | exGen _ hfree ih => exact .exGen ih hfree
  | propBot => exact .propBot
  | propOr => exact .propOr
  | propEx hfree => exact .propEx hfree
  | framing _ ih => exact .framing ih
  | existence => exact .existence
  | singleton C₁ C₂ => exact .singleton C₁ C₂
end Provable
end MatchingLogic
