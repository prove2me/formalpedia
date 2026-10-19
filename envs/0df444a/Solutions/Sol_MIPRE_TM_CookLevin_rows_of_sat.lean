-- Prove2me | solution 1 for MIPRE.TM.CookLevin.rows_of_sat
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:32:58.981349+00:00
-- url     : https://prove2.me/submissions/4908e10e-453c-4acc-9f20-aae5602fb58b

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/CookLevin/Sound.lean (solution of MIPRE.TM.CookLevin.rows_of_sat);
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
import Theorems.Thm_MIPRE_TM_CookLevin_inputPos_cfgAt_le
import Theorems.Thm_MIPRE_TM_CookLevin_rowOk_step
import Theorems.Thm_MIPRE_TM_CookLevin_rowOk_zero
import Theorems.Thm_MIPRE_TM_CookLevin_sat_window
import Theorems.Thm_MIPRE_TM_CookLevin_workTapePos_cfgAt_bounds

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace Turing.MultiInputTM
section
open Relation
open MultiTapeTM (moveInputPos)
open Cfg
variable {i w : ℕ} {State Symbol : Type*}
variable {tm : MultiInputTM i w Symbol State}
variable {input : Fin i → List Symbol}
/-- The output produced in `t + 1` steps is the output produced in `t` steps followed by
the symbol (optionally) emitted at step `t`. -/
lemma outputString_succ
    (tm : MultiInputTM i w Symbol State)
    (cfg : Cfg i w Symbol State input) (t : ℕ) :
    tm.outputString cfg (t + 1) =
      tm.outputString cfg t ++ (tm.outputSymbol (tm.configs cfg t)).toList := by
  simp [outputString, List.range_succ, List.flatMap_append]
end
end Turing.MultiInputTM

namespace MIPRE.TM.CookLevin
section
open Turing SAT MultiInputTM
open MultiTapeTM (moveInputPos moveInputPos_zero)
variable {i w : ℕ} {Symbol State : Type*} [Fintype Symbol] [DecidableEq Symbol] [Fintype State]
  [DecidableEq State] {S : ℕ}
variable (M : MultiInputTM i w Symbol State) (acc : Symbol) {input : Fin i → List Symbol}
omit [Fintype Symbol] [DecidableEq Symbol] [Fintype State] [DecidableEq State] in
theorem cfgAt_succ (t : ℕ) : cfgAt M (input := input) (t + 1) = M.step (cfgAt M t) :=
  configs_succ_eq_step'
end
end MIPRE.TM.CookLevin

namespace MIPRE.TM.CookLevin
section
open Turing SAT MultiInputTM
open MultiTapeTM (moveInputPos)
variable {i w : ℕ} {Symbol State : Type*} [Fintype Symbol] [DecidableEq Symbol] [Fintype State]
  [DecidableEq State] {S : ℕ}
  (M : MultiInputTM i w Symbol State) (acc : Symbol) {input : Fin i → List Symbol}
omit [Fintype Symbol] [DecidableEq Symbol] [Fintype State] [DecidableEq State] in
theorem cfgAt_zero : cfgAt M (input := input) 0 = M.initCfg input := configs_zero
end
end MIPRE.TM.CookLevin

namespace MIPRE.TM.CookLevin
section
open Turing SAT MultiInputTM
open MultiTapeTM (moveInputPos)
variable {i w : ℕ} {Symbol State : Type*} [Fintype Symbol] [DecidableEq Symbol] [Fintype State]
  [DecidableEq State] {S : ℕ}
  (M : MultiInputTM i w Symbol State) (acc : Symbol) {input : Fin i → List Symbol}
omit [Fintype Symbol] [Fintype State] [DecidableEq State] [DecidableEq Symbol] in
/-- At every time `t ≤ S`, every head of the run is on an interior cell. -/
theorem headsIn_cfgAt (t : ℕ) (ht : t ≤ S) : HeadsIn (cfgAt M (input := input) t) S where
  input_pos j := by have := inputPos_cfgAt_le M (input := input) t j; omega
  work_pos j := by have := workTapePos_cfgAt_bounds M (input := input) t j; omega
end
end MIPRE.TM.CookLevin

namespace MIPRE.TM.CookLevin
section
open Turing SAT MultiInputTM
open MultiTapeTM (moveInputPos)
variable {i w : ℕ} {Symbol State : Type*} [Fintype Symbol] [DecidableEq Symbol] [Fintype State]
  [DecidableEq State] {S : ℕ}
  (M : MultiInputTM i w Symbol State) (acc : Symbol) {input : Fin i → List Symbol}
omit [Fintype Symbol] [DecidableEq Symbol] [Fintype State] [DecidableEq State] in
theorem outputString_zero (c : Cfg i w Symbol State input) : M.outputString c 0 = [] := by
  simp [outputString]
end
end MIPRE.TM.CookLevin

namespace MIPRE.TM.CookLevin
section
open Turing SAT MultiInputTM
open MultiTapeTM (moveInputPos)
variable {i w : ℕ} {Symbol State : Type*} [Fintype Symbol] [DecidableEq Symbol] [Fintype State]
  [DecidableEq State] {S : ℕ}
  (M : MultiInputTM i w Symbol State) (acc : Symbol) {input : Fin i → List Symbol}
omit [Fintype Symbol] [DecidableEq Symbol] [Fintype State] [DecidableEq State] in
theorem outputString_succ' (t : ℕ) :
    M.outputString (M.initCfg input) (t + 1) =
      M.outputString (M.initCfg input) t ++ (M.outputSymbol (cfgAt M (input := input) t)).toList :=
  outputString_succ M _ t
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
omit [Fintype Symbol] [Fintype State] [DecidableEq Symbol] [DecidableEq State] in
theorem imp2_eval (f : TabVar i w Symbol State S G → Bool) (a b : TabVar i w Symbol State S G) :
    (imp2 a b).eval f = true ↔ (f a = true → f b = true) := by
  cases ha : f a <;> cases hb : f b <;> simp [imp2, cl, Clause3.eval, Lit.eval, ha, hb]
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
omit [Fintype Symbol] [Fintype State] [DecidableEq Symbol] [DecidableEq State] in
theorem nand2_eval (f : TabVar i w Symbol State S G → Bool) (a b : TabVar i w Symbol State S G) :
    (nand2 a b).eval f = true ↔ ¬ (f a = true ∧ f b = true) := by
  cases ha : f a <;> cases hb : f b <;> simp [nand2, cl, Clause3.eval, Lit.eval, ha, hb]
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
omit [Fintype Symbol] [Fintype State] [DecidableEq Symbol] [DecidableEq State] in
theorem cl_eval (f : TabVar i w Symbol State S G → Bool) (l₁ l₂ l₃ : Lit (TabVar i w Symbol State S G)) :
    (cl l₁ l₂ l₃).eval f = true ↔ l₁.eval f = true ∨ l₂.eval f = true ∨ l₃.eval f = true := by
  simp [cl, Clause3.eval, or_assoc]
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
theorem sat_bdry_cell (t : Fin (S + 1)) (d : Tape i w) (p : Pos S) (v : CellVal Symbol)
    (hb : p.IsBdry) : a (.cell t d p v) = decide (v = .bdry) :=
  (unit_eval _ _ _).mp (hSat _ (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl ⟨t, d, p, v, hb, rfl⟩))))))
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
theorem sat_bdry_head (t : Fin (S + 1)) (d : Tape i w) (p : Pos S) (hb : p.IsBdry) :
    a (.head t d p) = false :=
  (unit_eval _ _ _).mp (hSat _ (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr ⟨t, d, p, hb, rfl⟩))))))
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
theorem sat_emitted_zero : a (.emitted 0) = false :=
  (unit_eval _ _ _).mp (hSat _ (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl
    (Or.inl rfl)))))))))
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
theorem sat_emitted_succ (t : Fin S) :
    a (.emitted t.succ) = true → a (.emitted t.castSucc) = true ∨ a (.emitOne t) = true := by
  have := hSat _ (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨t, rfl⟩))))))))
  rw [cl_eval] at this
  simp only [lit_eval_true, lit_eval_false, Bool.not_eq_eq_eq_not, Bool.not_true] at this
  intro h
  rcases this with h' | h' | h'
  · rw [h] at h'; exact Bool.noConfusion h'
  · exact Or.inl h'
  · exact Or.inr h'
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
theorem sat_emitted_mono (t : Fin S) :
    a (.emitted t.castSucc) = true → a (.emitted t.succ) = true :=
  (imp2_eval _ _ _).mp
    (hSat _ (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr ⟨t, rfl⟩))))))))
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
theorem sat_emitOne_emitted (t : Fin S) :
    a (.emitOne t) = true → a (.emitted t.succ) = true :=
  (imp2_eval _ _ _).mp (hSat _ (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr ⟨t, rfl⟩)))))))
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
theorem sat_emitOne_once (t : Fin S) :
    ¬ (a (.emitOne t) = true ∧ a (.emitted t.castSucc) = true) :=
  (nand2_eval _ _ _).mp (hSat _ (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr ⟨t, rfl⟩))))))
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
theorem sat_emitBad (t : Fin S) : a (.emitBad t) = false :=
  (unit_eval _ _ _).mp (hSat _ (Or.inl (Or.inl (Or.inr (Or.inr ⟨t, rfl⟩)))))
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
theorem _root_.solution (hchk : IsCheckCircuit M acc chk) (hC : chk.RefsLt) (hin : chk.InputsLt)
    (hne : chk.gates ≠ []) (t : ℕ) (ht : t ≤ S) :
    RowOk (input := inputOf s₀ s₁ fixed chk a) a ⟨t, Nat.lt_succ_of_le ht⟩ (cfgAt M t) ∧
      a (.emitted ⟨t, Nat.lt_succ_of_le ht⟩) =
        decide (M.outputString (M.initCfg (inputOf s₀ s₁ fixed chk a)) t ≠ []) ∧
      (M.outputString (M.initCfg (inputOf s₀ s₁ fixed chk a)) t).length ≤ 1 ∧
      ∀ s ∈ M.outputString (M.initCfg (inputOf s₀ s₁ fixed chk a)) t, s = acc := by
  induction t with
  | zero =>
    refine ⟨?_, ?_, by simp [outputString_zero], by simp [outputString_zero]⟩
    · rw [cfgAt_zero]
      exact rowOk_zero M s₀ s₁ fixed chk a hSat
    · rw [show (⟨0, Nat.lt_succ_of_le ht⟩ : Fin (S + 1)) = 0 from rfl,
        sat_emitted_zero M s₀ s₁ fixed chk a hSat]
      simp [outputString_zero]
  | succ t ih =>
    obtain ⟨hrow, hem, hlen, hacc⟩ := ih (by omega)
    set input := inputOf s₀ s₁ fixed chk a with hinput
    let tf : Fin S := ⟨t, by omega⟩
    have hstep := rowOk_step M acc a tf (cfgAt M (input := input) t) hrow
      (headsIn_cfgAt M (input := input) t (by omega))
      (by rw [← cfgAt_succ]; exact headsIn_cfgAt M (input := input) (t + 1) ht)
      (fun js => sat_window M acc s₀ s₁ fixed chk a hSat hchk hC hin hne tf js)
      (fun d p v hb => sat_bdry_cell M s₀ s₁ fixed chk a hSat _ d p v hb)
      (fun d p hb => sat_bdry_head M s₀ s₁ fixed chk a hSat _ d p hb)
    obtain ⟨hrow', hone, hbad⟩ := hstep
    have hem' : a (.emitted tf.castSucc) =
        decide (M.outputString (M.initCfg input) t ≠ []) := hem
    have hbad' := sat_emitBad M s₀ s₁ fixed chk a hSat tf
    rw [hbad] at hbad'
    have hsym : M.outputSymbol (cfgAt M (input := input) t) = none ∨
        M.outputSymbol (cfgAt M (input := input) t) = some acc := by
      by_cases h : M.outputSymbol (cfgAt M (input := input) t) = none
      · exact Or.inl h
      · right
        by_contra h'
        exact absurd hbad' (by simp [h, h'])
    rw [outputString_succ']
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [cfgAt_succ]; exact hrow'
    · apply Bool.eq_iff_iff.mpr
      rw [decide_eq_true_iff]
      constructor
      · intro h
        rcases sat_emitted_succ M s₀ s₁ fixed chk a hSat tf h with h' | h'
        · rw [hem', decide_eq_true_iff] at h'
          exact fun h'' => h' (List.append_eq_nil_iff.mp h'').1
        · rw [hone, decide_eq_true_iff] at h'
          rw [h']; simp
      · intro h
        by_cases hA : M.outputString (M.initCfg input) t = []
        · rw [hA, List.nil_append] at h
          rcases hsym with h' | h'
          · rw [h'] at h; exact absurd rfl h
          · exact sat_emitOne_emitted M s₀ s₁ fixed chk a hSat tf
              (by rw [hone, h']; simp)
        · exact sat_emitted_mono M s₀ s₁ fixed chk a hSat tf (by rw [hem']; exact decide_eq_true hA)
    · rcases hsym with h' | h'
      · rw [h']; simpa using hlen
      · have hnot := sat_emitOne_once M s₀ s₁ fixed chk a hSat tf
        rw [hone, h', hem'] at hnot
        have hA : M.outputString (M.initCfg input) t = [] := by
          by_contra hA
          exact hnot ⟨by simp, decide_eq_true hA⟩
        rw [hA, h']; simp
    · intro s hs
      rw [List.mem_append] at hs
      rcases hs with hs | hs
      · exact hacc s hs
      · rcases hsym with h' | h'
        · rw [h'] at hs; simp at hs
        · rw [h'] at hs; simpa using hs
end MIPRE.TM.CookLevin
