-- Prove2me | solution 1 for Monodromy.Counter.Reversible.Recording.embed_injective
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T19:21:24.485605+00:00
-- url     : https://prove2.me/submissions/e416734e-1a92-463c-876b-f1bfdc67e219

module
public import Definitions.Def_Monodromy_Counter
public import Mathlib.Data.Fin.Basic
public import Mathlib.Logic.Function.Basic

@[expose] public section

open Monodromy
open Monodromy.Counter
open Monodromy.Counter.Reversible
open Monodromy.Counter.Reversible.Recording
variable {n m : ℕ}

theorem solution : Function.Injective (@embed n m) := by
  rintro ⟨⟨first_pc, first_values⟩, first_history⟩
    ⟨⟨second_pc, second_values⟩, second_history⟩ same
  change framed (dispatch first_pc) first_values first_history 0 =
    framed (dispatch second_pc) second_values second_history 0 at same
  apply Prod.ext
  · apply congrArg₂ Counter.Configuration.mk
    · have controls := congrArg (fun state : State (n + 2) (size m) => state.1) same
      exact ((copy_eq_iff first_pc second_pc _ _).mp controls).1
    · funext index
      have values := congrArg
        (fun state : State (n + 2) (size m) => state.2 (Fin.castAdd 2 index)) same
      exact Int.natCast_inj.mp (by simpa [framed, frame] using values)
  · have histories := congrArg
      (fun state : State (n + 2) (size m) => state.2 (historyRegister n 0)) same
    exact Int.natCast_inj.mp (by simpa [framed, frame, historyRegister] using histories)
