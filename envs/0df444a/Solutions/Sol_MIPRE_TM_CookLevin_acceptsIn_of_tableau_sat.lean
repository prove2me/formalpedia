-- Prove2me | solution 1 for MIPRE.TM.CookLevin.acceptsIn_of_tableau_sat
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:34:03.48699+00:00
-- url     : https://prove2.me/submissions/9ec0e01b-d744-4772-b148-563650942701

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/CookLevin/Sound.lean (solution of MIPRE.TM.CookLevin.acceptsIn_of_tableau_sat);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Computability.Language
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Set.Basic
import Mathlib.Data.Sign.Defs
import Mathlib.Logic.Relation
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_SAT_Cnf
import Definitions.Def_MIPRE_Cslib_Foundations_Data_RelatesInSteps
import Definitions.Def_MIPRE_Cslib_Computability_Machines_Turing_MultiTape_Deterministic
import Definitions.Def_MIPRE_TM_MultiInput_Deterministic
import Definitions.Def_MIPRE_TM_CookLevin_Local
import Definitions.Def_MIPRE_Foundations_SAT_Tseitin
import Definitions.Def_MIPRE_TM_CookLevin_Tableau
import Definitions.Def_MIPRE_TM_CookLevin_Semantics
import Definitions.Def_MIPRE_TM_CookLevin_Correct
import Definitions.Def_MIPRE_TM_CookLevin_Sound
import Theorems.Thm_MIPRE_TM_CookLevin_rowOk_zero
import Theorems.Thm_MIPRE_TM_CookLevin_rows_of_sat

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.TM.CookLevin
section
open Turing SAT MultiInputTM
open MultiTapeTM (moveInputPos)
variable {i w : ℕ} {Symbol State : Type*} [Fintype Symbol] [DecidableEq Symbol] [Fintype State]
  [DecidableEq State] {S : ℕ}
  (M : MultiInputTM i w Symbol State) (acc : Symbol) {input : Fin i → List Symbol}
variable (chk : Circuit)
variable {G : ℕ}
omit [Fintype Symbol] [Fintype State] [DecidableEq Symbol] [DecidableEq State] in
theorem unit_eval (f : TabVar i w Symbol State S G → Bool) (v : TabVar i w Symbol State S G)
    (b : Bool) : (unit v b).eval f = true ↔ f v = b := by
  cases b <;> cases h : f v <;> simp [unit, cl, Clause3.eval, Lit.eval, h]
end
end MIPRE.TM.CookLevin

namespace MIPRE.TM.CookLevin
section
open Turing SAT MultiInputTM
open MultiTapeTM (moveInputPos)
variable {i w : ℕ} {Symbol State : Type*} [Fintype Symbol] [DecidableEq Symbol] [Fintype State]
  [DecidableEq State] {S : ℕ}
  (M : MultiInputTM i w Symbol State) (acc : Symbol) {input : Fin i → List Symbol}
variable (chk : Circuit)
variable {G : ℕ}
omit [Fintype Symbol] [Fintype State] [DecidableEq State] [DecidableEq Symbol] in
theorem cellValAt_inl (c : Cfg i w Symbol State input) (j : Fin i) (p : Pos S) :
    cellValAt (S := S) c (.inl j) p = inputCellVal (input j) p := rfl
end
end MIPRE.TM.CookLevin

namespace MIPRE.TM.CookLevin
section
open Turing SAT MultiInputTM
variable {i w : ℕ} {Symbol State : Type*} [Fintype Symbol] [DecidableEq Symbol] [Fintype State]
  [DecidableEq State] {S G : ℕ}
omit [Fintype Symbol] [DecidableEq Symbol] [Fintype State] [DecidableEq State] in
theorem freeString_mem (a : TabVar i w Symbol State S G → Bool) (j : Fin i) (s₀ s₁ : Symbol) :
    ∀ s ∈ freeString a j s₀ s₁, s = s₀ ∨ s = s₁ := by
  intro s hs
  rw [freeString, List.mem_ofFn] at hs
  obtain ⟨k, hk⟩ := hs
  split_ifs at hk
  · exact Or.inl hk.symm
  · exact Or.inr hk.symm
end
end MIPRE.TM.CookLevin

namespace MIPRE.TM.CookLevin
section
open Turing SAT MultiInputTM
theorem eq_singleton_of_length_le_one {α : Type*} {l : List α} {x : α} (hne : l ≠ [])
    (hlen : l.length ≤ 1) (hall : ∀ s ∈ l, s = x) : l = [x] := by
  cases l with
  | nil => exact absurd rfl hne
  | cons s l' =>
    cases l' with
    | nil => rw [hall s (by simp)]
    | cons s' l'' => simp at hlen
end
end MIPRE.TM.CookLevin

namespace MIPRE.TM.CookLevin
section
open Turing SAT MultiInputTM
variable {i w : ℕ} {Symbol State : Type*} [Fintype Symbol] [DecidableEq Symbol] [Fintype State]
  [DecidableEq State] {S : ℕ}
  (M : MultiInputTM i w Symbol State) (acc s₀ s₁ : Symbol) (fixed : Fin i → Option (List Symbol))
  (chk : Circuit) (a : TabVar i w Symbol State S chk.gates.length → Bool)
omit [Fintype Symbol] [DecidableEq Symbol] [Fintype State] [DecidableEq State] in
theorem inputOf_fixed (j : Fin i) (x : List Symbol) (hx : fixed j = some x) :
    inputOf s₀ s₁ fixed chk a j = x := by
  simp [inputOf, hx]
end
end MIPRE.TM.CookLevin

namespace MIPRE.TM.CookLevin
section
open Turing SAT MultiInputTM
variable {i w : ℕ} {Symbol State : Type*} [Fintype Symbol] [DecidableEq Symbol] [Fintype State]
  [DecidableEq State] {S : ℕ}
  (M : MultiInputTM i w Symbol State) (acc s₀ s₁ : Symbol) (fixed : Fin i → Option (List Symbol))
  (chk : Circuit) (a : TabVar i w Symbol State S chk.gates.length → Bool)
omit [Fintype Symbol] [DecidableEq Symbol] [Fintype State] [DecidableEq State] in
theorem inputOf_free (j : Fin i) (hx : fixed j = none) :
    inputOf s₀ s₁ fixed chk a j = freeString a j s₀ s₁ := by
  simp [inputOf, hx]
end
end MIPRE.TM.CookLevin

namespace MIPRE.TM.CookLevin
section
open Turing SAT MultiInputTM
variable {i w : ℕ} {Symbol State : Type*} [Fintype Symbol] [DecidableEq Symbol] [Fintype State]
  [DecidableEq State] {S : ℕ}
  (M : MultiInputTM i w Symbol State) (acc s₀ s₁ : Symbol) (fixed : Fin i → Option (List Symbol))
  (chk : Circuit) (a : TabVar i w Symbol State S chk.gates.length → Bool)
variable (hSat : (tableau M s₀ s₁ S fixed chk).Sat a)
include hSat
theorem sat_final_state : a (.state (Fin.last S) none) = true :=
  (unit_eval _ _ _).mp (hSat _ (Or.inl (Or.inr (Or.inl rfl))))
end
end MIPRE.TM.CookLevin

namespace MIPRE.TM.CookLevin
section
open Turing SAT MultiInputTM
variable {i w : ℕ} {Symbol State : Type*} [Fintype Symbol] [DecidableEq Symbol] [Fintype State]
  [DecidableEq State] {S : ℕ}
  (M : MultiInputTM i w Symbol State) (acc s₀ s₁ : Symbol) (fixed : Fin i → Option (List Symbol))
  (chk : Circuit) (a : TabVar i w Symbol State S chk.gates.length → Bool)
variable (hSat : (tableau M s₀ s₁ S fixed chk).Sat a)
include hSat
theorem sat_final_emitted : a (.emitted (Fin.last S)) = true :=
  (unit_eval _ _ _).mp (hSat _ (Or.inl (Or.inr (Or.inr rfl))))
end
end MIPRE.TM.CookLevin

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.TM.CookLevin
open Turing SAT MultiInputTM
variable {i w : ℕ} {Symbol State : Type*} [Fintype Symbol] [DecidableEq Symbol] [Fintype State]
  [DecidableEq State] {S : ℕ}
  (M : MultiInputTM i w Symbol State) (acc s₀ s₁ : Symbol) (fixed : Fin i → Option (List Symbol))
  (chk : Circuit) (a : TabVar i w Symbol State S chk.gates.length → Bool)
variable (hSat : (tableau M s₀ s₁ S fixed chk).Sat a)
include hSat
theorem _root_.solution (hchk : IsCheckCircuit M acc chk) (hC : chk.RefsLt)
    (hin : chk.InputsLt) (hne : chk.gates ≠ []) :
    (∀ j x, fixed j = some x → inputOf s₀ s₁ fixed chk a j = x) ∧
    (∀ j, fixed j = none → ∀ s ∈ inputOf s₀ s₁ fixed chk a j, s = s₀ ∨ s = s₁) ∧
    (∀ j (p : Pos S) v, a (.cell 0 (.inl j) p v) =
      decide (v = inputCellVal (inputOf s₀ s₁ fixed chk a j) p)) ∧
    AcceptsIn M acc (inputOf s₀ s₁ fixed chk a) S := by
  obtain ⟨hrow, hem, hlen, hacc⟩ :=
    rows_of_sat M acc s₀ s₁ fixed chk a hSat hchk hC hin hne S le_rfl
  refine ⟨fun j x hx => inputOf_fixed s₀ s₁ fixed chk a j x hx, fun j hj => ?_, fun j p v => ?_, ?_, ?_⟩
  · rw [inputOf_free s₀ s₁ fixed chk a j hj]
    exact freeString_mem a j s₀ s₁
  · have := (rowOk_zero M s₀ s₁ fixed chk a hSat).cell (.inl j) p v
    rw [this, cellValAt_inl]
    exact decide_eq_decide.mpr eq_comm
  · have h := sat_final_state M s₀ s₁ fixed chk a hSat
    have h' := hrow.state none
    rw [show (Fin.last S) = ⟨S, Nat.lt_succ_of_le le_rfl⟩ from rfl, h', decide_eq_true_iff] at h
    exact h
  · have h := sat_final_emitted M s₀ s₁ fixed chk a hSat
    rw [show (Fin.last S) = ⟨S, Nat.lt_succ_of_le le_rfl⟩ from rfl, hem, decide_eq_true_iff] at h
    exact eq_singleton_of_length_le_one h hlen hacc
end MIPRE.TM.CookLevin
