-- Prove2me | solution 1 for GwExact.rank_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T20:24:31.720214+00:00
-- url     : https://prove2.me/submissions/6c1716ae-cfb3-44d3-a47e-dcc8da8d5b03

module
public import Definitions.Def_GwExact_Defs
public import Definitions.Def_GwExact_Clauses
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Fin
public import Definitions.Def_GwExact_Rank
public import Theorems.Thm_GwExact_firstPos_spec
public import Theorems.Thm_GwExact_firstPos_congr
public import Theorems.Thm_GwExact_rank_lt_rank

set_option autoImplicit true
@[expose] public section
public section
open GwExact
variable {α : Type*} [DecidableEq α] (f : ℕ → α)
namespace GwExact
theorem _root_.solution {i i' : ℕ} : rank f i = rank f i' ↔ f i = f i' := by
  constructor
  · intro h
    by_contra hne
    have hp : firstPos f i ≠ firstPos f i' := fun hp =>
      hne ((firstPos_spec f i).symm.trans ((congrArg f hp).trans (firstPos_spec f i')))
    rcases Nat.lt_or_gt_of_ne hp with hlt | hlt
    · have := rank_lt_rank f hlt
      omega
    · have := rank_lt_rank f hlt
      omega
  · intro h
    unfold rank
    rw [firstPos_congr f h]
end GwExact
