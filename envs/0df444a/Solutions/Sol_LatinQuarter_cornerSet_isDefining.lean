-- Prove2me | solution 1 for LatinQuarter.cornerSet_isDefining
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:22:44.587562+00:00
-- url     : https://prove2.me/submissions/07c64ca5-cce2-428b-9be3-cae86c3a898c

module
public import Mathlib.Algebra.Group.Fin.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_LatinQuarter_Basic
public import Definitions.Def_LeanPool_LatinQuarter_Cyclic
public import Theorems.Thm_LatinQuarter_cyclic_isLatin
public import Theorems.Thm_LatinQuarter_corner_forcing_step

set_option autoImplicit true
@[expose] public section
public section
open LatinQuarter
namespace LatinQuarter
theorem _root_.solution (n : ℕ) (hn : 0 < n) :
    IsDefining (cornerSet n) (cyclic n) := by
  refine ⟨cyclic_isLatin n hn, ?_⟩
  intro M hM ha
  have all : ∀ m : ℕ, ∀ r c : Fin n, fillingOrder r c = m → M r c = cyclic n r c := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro r c hrc
      apply corner_forcing_step hn M hM ha r c
      intro i j hij
      exact ih (fillingOrder i j) (by omega) i j rfl
  funext r c
  exact all _ r c rfl
end LatinQuarter
