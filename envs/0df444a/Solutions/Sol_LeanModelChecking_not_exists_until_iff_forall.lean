-- Prove2me | solution 1 for LeanModelChecking.not_exists_until_iff_forall
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:44:09.386345+00:00
-- url     : https://prove2.me/submissions/d58b8597-e08b-480b-a5b0-086f28888ad3

module
public import Definitions.Def_LeanPool_LeanModelChecking_LTLNBWStatement
public import Aesop.BuiltinRules
public import Mathlib.Tactic.Finiteness.Attr
public import Mathlib.Tactic.Push
public import Definitions.Def_LeanPool_LeanModelChecking_LTLNNF

set_option autoImplicit true
@[expose] public section
public section
open LeanModelChecking
namespace LeanModelChecking
theorem _root_.solution {P Q : Nat → Prop} :
    (¬ ∃ i, Q i ∧ ∀ k < i, P k) ↔ ∀ i, ¬ Q i ∨ ∃ k < i, ¬ P k := by
  classical
  constructor
  · intro h i
    rcases Classical.em (Q i) with hQi | hQi
    · simp_all
    · exact Or.inl hQi
  · rintro h ⟨i, hQi, hPi⟩
    rcases h i with hneg | ⟨k, hk, hk'⟩
    · exact hneg hQi
    · exact hk' (hPi k hk)
end LeanModelChecking
