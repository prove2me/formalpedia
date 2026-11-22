-- Prove2me | solution 1 for MatchingLogic.Sorted.satSetHet_homogeneous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:45:52.171128+00:00
-- url     : https://prove2.me/submissions/6fbb5d09-bcd5-4a06-ba53-98a526ed43e1

module
public import Aesop.BuiltinRules
public import Mathlib.Order.SetNotation
public import Mathlib.Tactic.ToAdditive
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Lattice.Image
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Lattice
public import Definitions.Def_LeanPool_MatchingLogic_Sorted

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open MatchingLogic.Sorted
variable {S : MSignature} {Var : Type}
namespace MatchingLogic.Sorted
theorem _root_.solution (M : MModel S) {s : S.Srt}
    (Γ : Set (MPattern S Var s)) :
    M.SatSet Γ ↔ M.SatSetHet {p | ∃ γ ∈ Γ, p = ⟨s, γ⟩} := by
  constructor
  · intro h p hp
    rcases hp with ⟨γ, hγ, rfl⟩
    exact h γ hγ
  · intro h γ hγ
    exact h ⟨s, γ⟩ ⟨γ, hγ, rfl⟩
end MatchingLogic.Sorted
