-- Prove2me | solution 1 for NoAdjString.card_noAdjacentStrings
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-25T17:31:38.229393+00:00
-- url     : https://prove2.me/submissions/f998c4bd-ce3c-4915-b008-0731f03a9a51

import Definitions.Def_NoAdjacentGapEquiv
import Mathlib.Data.Nat.Fib.Basic

open Finset Function NoAdjString

theorem solution (n : ℕ) :
    (noAdjacentStrings n).card = Nat.fib (n + 2) := by
  let hc : ∀ m : ℕ, (noAdjacentStrings m).card =
      Fintype.card {f : Fin m → Bool // f ∈ noAdjacentStrings m} := fun m => by
    classical
    rw [Fintype.card_subtype (fun f : Fin m → Bool => f ∈ noAdjacentStrings m)]
    have h5 : ∀ (f : Fin m → Bool), f ∈ noAdjacentStrings m ↔ NoAdjacentOnes f := fun f => by
      simp [noAdjacentStrings, Finset.mem_filter]
    have h4 : Finset.univ.filter (fun f : Fin m → Bool => f ∈ noAdjacentStrings m) =
        noAdjacentStrings m := by
      ext f
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [h4]
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 =>
      have hall : ∀ (g : Fin 0 → Bool), NoAdjacentOnes g := by
        intro g i hnext; omega
      have h0 : noAdjacentStrings 0 = Finset.univ := by
        ext f
        simp only [noAdjacentStrings, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun _ => trivial, fun _ => hall f⟩
      rw [h0]; simp
    | 1 =>
      have hall : ∀ (g : Fin 1 → Bool), NoAdjacentOnes g := by
        intro g i hnext; omega
      have h1 : noAdjacentStrings 1 = Finset.univ := by
        ext f
        simp only [noAdjacentStrings, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun _ => trivial, fun _ => hall f⟩
      rw [h1]; rfl
    | n + 2 =>
      rw [hc (n + 2),
        Fintype.card_congr (noAdjacentStringsRecurrenceEquiv n),
        Fintype.card_sum, ←hc (n + 1), ←hc n,
        ih n (by omega), ih (n + 1) (by omega)]
      rw [Nat.fib_add_two (n := n + 2)]
      ring
