-- Prove2me | solution 2 for Monodromy.Observation.exists_bounded_visit
-- status  : ACCEPTED   (prove)
-- author  : @Xiaoyang Liu
-- created : 2026-11-06T14:58:37.164555+00:00
-- url     : https://prove2.me/submissions/fe5947c6-d977-4349-be67-78b67d42b5b8

-- Generated mechanically from the frozen source; no own-target import.
module
public import Definitions.Def_Monodromy_Observation
public import Lean.Elab.Tactic.Omega
public import Mathlib.Computability.StateTransition
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Set.Finite.Basic

@[expose] public section


-- Original target, hoisted to top-level theorem solution.
open Monodromy
open Monodromy.Observation
variable {S : Type*}
theorem solution [Fintype S] (next : S → S) (visit : S → Bool) (state : S)
    (eventually : ∃ rounds : ℕ, visit ((next^[rounds]) state) = true) :
    ∃ rounds < Fintype.card S, visit ((next^[rounds]) state) = true := by
  classical
  let first := Nat.find eventually
  have visits : visit ((next^[first]) state) = true := Nat.find_spec eventually
  have no_repeat (left right : Fin (first + 1)) (ordered : left.val < right.val)
      (same : (next^[left.val]) state = (next^[right.val]) state) : False := by
    have repeated := congrArg (next^[first - right.val]) same
    rw [← Function.iterate_add_apply, ← Function.iterate_add_apply] at repeated
    have end_index : first - right.val + right.val = first := by omega
    rw [end_index] at repeated
    have earlier : first - right.val + left.val < first := by omega
    exact Nat.find_min eventually earlier (by rw [repeated]; exact visits)
  have fresh : Function.Injective (fun index : Fin (first + 1) => (next^[index.val]) state) := by
    intro left right same
    apply Fin.ext
    by_contra different
    rcases lt_or_gt_of_ne different with ordered | ordered
    · exact no_repeat left right ordered same
    · exact no_repeat right left ordered same.symm
  have bound : first + 1 ≤ Fintype.card S := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective _ fresh
  exact ⟨first, by omega, visits⟩
