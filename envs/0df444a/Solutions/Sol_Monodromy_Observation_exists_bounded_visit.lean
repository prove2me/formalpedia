-- Prove2me | solution 1 for Monodromy.Observation.exists_bounded_visit
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T19:36:26.828257+00:00
-- url     : https://prove2.me/submissions/c17af5c8-586b-40e4-b67c-c997784eeef6

module
public import Definitions.Def_Monodromy_Observation
public import Lean.Elab.Tactic.Omega
public import Mathlib.Computability.StateTransition
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Set.Finite.Basic

@[expose] public section

open Monodromy
open Monodromy.Observation
variable {S : Type*}

theorem solution [Fintype S] (next : S → S) (visit : S → Bool) (state : S)
    (eventually : ∃ rounds : ℕ, visit ((next^[rounds]) state) = true) :
    ∃ rounds < Fintype.card S, visit ((next^[rounds]) state) = true := by
  classical
  let m := Nat.find eventually
  have hm : visit ((next^[m]) state) = true := by
    simpa [m] using Nat.find_spec eventually
  refine ⟨m, ?_, hm⟩
  by_contra hbound
  have hcard : Fintype.card S ≤ m := by omega
  let orbit : Fin (m + 1) → S := fun i => (next^[i.val]) state
  have hnoninj : ¬Function.Injective orbit := by
    apply Fintype.not_injective_of_card_lt orbit
    simpa using Nat.lt_succ_of_le hcard
  obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hnoninj
  have earlier_of_lt : ∀ {i j : Fin (m + 1)}, i < j → orbit i = orbit j →
      ∃ k < m, visit ((next^[k]) state) = true := by
    intro i j hij heq
    have hj : (j : ℕ) ≤ m := by omega
    have hlt : m - (j : ℕ) + (i : ℕ) < m := by omega
    refine ⟨m - (j : ℕ) + (i : ℕ), hlt, ?_⟩
    have happ := congrArg (fun x => (next^[m - (j : ℕ)]) x) heq
    dsimp [orbit] at happ
    rw [← Function.iterate_add_apply, ← Function.iterate_add_apply,
      Nat.sub_add_cancel hj] at happ
    rw [happ]
    exact hm
  rcases lt_or_gt_of_ne hne with hijlt | hjilt
  · obtain ⟨k, hkm, hk⟩ := earlier_of_lt hijlt hij
    exact Nat.find_min eventually hkm hk
  · obtain ⟨k, hkm, hk⟩ := earlier_of_lt hjilt hij.symm
    exact Nat.find_min eventually hkm hk
