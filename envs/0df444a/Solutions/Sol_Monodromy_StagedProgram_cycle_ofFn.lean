-- Prove2me | solution 1 for Monodromy.StagedProgram.cycle_ofFn
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:09:29.918673+00:00
-- url     : https://prove2.me/submissions/657be043-945f-4c53-a9be-4d7bc7a70e33

module
public import Definitions.Def_Monodromy_Continuation
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Logic.Function.Conjugate

@[expose] public section

open Monodromy
open Monodromy.StagedProgram
open CoupledContinuation
open Fin.NatCast
variable (count degree : ℕ) [NeZero count] [NeZero degree]

theorem solution (stages : Fin count → Program degree) (state : Memory) :
    ((compile count degree stages).advance)^[count] (embed count 0 state) =
      embed count 0 ((List.ofFn stages).foldl
        (fun point program => program.advance point) state) := by
  have take_succ (n : ℕ) (hn : n < count) :
      (List.ofFn stages).take (n + 1) =
        (List.ofFn stages).take n ++ [stages (n : Fin count)] := by
    rw [List.take_add_one, List.getElem?_ofFn]
    have hfin : (⟨n, hn⟩ : Fin count) = (n : Fin count) := by
      apply Fin.ext
      simp [Fin.val_natCast, Nat.mod_eq_of_lt hn]
    simp [hn, hfin]
  have partial_cycle (n : ℕ) (hn : n ≤ count) :
      ((compile count degree stages).advance)^[n] (embed count 0 state) =
        embed count (n : Fin count)
          (((List.ofFn stages).take n).foldl
            (fun point program => program.advance point) state) := by
    induction n with
    | zero => simp
    | succ n ih =>
        have hlt : n < count := Nat.lt_of_succ_le hn
        rw [Function.iterate_succ_apply', ih (Nat.le_of_lt hlt), advance_embed,
          take_succ n hlt]
        simp [List.foldl_append, finRotate_apply, Nat.cast_add, Nat.cast_one]
  have htake : (List.ofFn stages).take count = List.ofFn stages :=
    (List.take_eq_self_iff _).2 (by simp)
  simpa [htake] using partial_cycle count (Nat.le_refl count)
