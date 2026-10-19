-- Prove2me | solution 1 for MIPRE.TM.CookLevin.rowOk_zero
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:30:03.690976+00:00
-- url     : https://prove2.me/submissions/b954af42-ec91-41e8-b018-8ba7b81ef8e1

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/CookLevin/Sound.lean (solution of MIPRE.TM.CookLevin.rowOk_zero);
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
import Theorems.Thm_MIPRE_TM_CookLevin_FreeFacts_cell_eq

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
variable (s₀ s₁ : Symbol)
variable {s₀ s₁}
omit [Fintype Symbol] [Fintype State] [DecidableEq State] in
theorem freeFacts (fixed : Fin i → Option (List Symbol)) (a : TabVar i w Symbol State S G → Bool)
    (hSat : (freeClauses (S := S) (G := G) s₀ s₁ fixed).Sat a) (j : Fin i) (hj : fixed j = none) :
    FreeFacts s₀ s₁ a j where
  bdry p v hb := (unit_eval _ _ _).mp
    (hSat _ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨j, p, v, hj, hb, rfl⟩))))))
  other p v hnb h0 h1 hbl := (unit_eval _ _ _).mp
    (hSat _ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨j, p, v, hj, hnb, h0, h1, hbl, rfl⟩))))))
  two v := (unit_eval _ _ _).mp (hSat _ (Or.inl (Or.inl (Or.inl (Or.inr ⟨j, v, hj, rfl⟩)))))
  some p hnb := by
    have := hSat _ (Or.inl (Or.inl (Or.inr ⟨j, p, hj, hnb, rfl⟩)))
    rw [cl_eval] at this
    simpa using this
  once p v v' hnb hvv' := (nand2_eval _ _ _).mp
    (hSat _ (Or.inl (Or.inr ⟨j, p, v, v', hj, hnb, hvv', rfl⟩)))
  mono p p' h2 hnb' hpp' := (imp2_eval _ _ _).mp
    (hSat _ (Or.inr ⟨j, p, p', hj, h2, hnb', hpp', rfl⟩))
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
omit [Fintype Symbol] [Fintype State] [DecidableEq State] [DecidableEq Symbol] in
theorem headCell_initCfg_iff (input : Fin i → List Symbol) (d : Tape i w) (p : Pos S) :
    headCell (S := S) (M.initCfg input) d = (p : ℕ) ↔ p = startCell S d := by
  cases d with
  | inl j =>
    simp only [headCell, initCfg, startCell, Fin.ext_iff, Fin.val_one]
    push_cast; omega
  | inr j =>
    simp only [headCell, initCfg, startCell, Fin.ext_iff]
    omega
end
end MIPRE.TM.CookLevin

namespace MIPRE.TM.CookLevin
section
open Turing SAT MultiInputTM
variable {i w : ℕ} {Symbol State : Type*} [Fintype Symbol] [DecidableEq Symbol] [Fintype State]
  [DecidableEq State] {S : ℕ}
  (M : MultiInputTM i w Symbol State) (acc s₀ s₁ : Symbol) (fixed : Fin i → Option (List Symbol))
  (chk : Circuit) (a : TabVar i w Symbol State S chk.gates.length → Bool)
omit [Fintype Symbol] [Fintype State] [DecidableEq State] [DecidableEq Symbol] in
theorem cellValAt_initCfg_inr (input : Fin i → List Symbol) (j : Fin w) (p : Pos S) :
    cellValAt (S := S) (M.initCfg input) (.inr j) p = workCellVal₀ p := by
  unfold cellValAt workCellVal₀
  split_ifs <;> rfl
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
theorem sat_start : (startClauses (S := S) (G := chk.gates.length) M fixed).Sat a :=
  fun c hc => hSat c (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hc)))))
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
theorem sat_free : (freeClauses (S := S) (G := chk.gates.length) s₀ s₁ fixed).Sat a :=
  fun c hc => hSat c (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hc)))))
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
theorem _root_.solution : RowOk (input := inputOf s₀ s₁ fixed chk a) a 0 (M.initCfg _) where
  cell d p v := by
    cases d with
    | inl j =>
      rw [cellValAt_inl]
      cases hj : fixed j with
      | none =>
        rw [inputOf_free s₀ s₁ fixed chk a j hj,
          (freeFacts fixed a (sat_free M s₀ s₁ fixed chk a hSat) j hj).cell_eq p v]
        exact decide_eq_decide.mpr eq_comm
      | some x =>
        rw [inputOf_fixed s₀ s₁ fixed chk a j x hj,
          (unit_eval a _ _).mp (sat_start M s₀ s₁ fixed chk a hSat _
            (Or.inl (Or.inr ⟨j, x, p, v, hj, rfl⟩)))]
        exact decide_eq_decide.mpr eq_comm
    | inr j =>
      rw [cellValAt_initCfg_inr, (unit_eval a _ _).mp (sat_start M s₀ s₁ fixed chk a hSat _
        (Or.inr ⟨j, p, v, rfl⟩))]
      exact decide_eq_decide.mpr eq_comm
  head d p := by
    rw [(unit_eval a _ _).mp (sat_start M s₀ s₁ fixed chk a hSat _
      (Or.inl (Or.inl (Or.inl ⟨d, p, rfl⟩))))]
    exact decide_eq_decide.mpr (headCell_initCfg_iff M _ d p).symm
  state q := by
    rw [(unit_eval a _ _).mp (sat_start M s₀ s₁ fixed chk a hSat _
      (Or.inl (Or.inl (Or.inr ⟨q, rfl⟩))))]
    exact decide_eq_decide.mpr eq_comm
end MIPRE.TM.CookLevin
