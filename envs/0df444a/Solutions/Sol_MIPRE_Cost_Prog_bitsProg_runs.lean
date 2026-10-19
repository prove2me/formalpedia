-- Prove2me | solution 1 for MIPRE.Cost.Prog.bitsProg_runs
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-16T15:33:02.041471+00:00
-- url     : https://prove2.me/submissions/7637ed7b-894e-485b-9614-acf56697b788

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Repeat/DecMain.lean (solution of MIPRE.Cost.Prog.bitsProg_runs);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Computability.Primrec.List
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Halting_Descriptions
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Halting_Lists
import Definitions.Def_MIPRE_Foundations_Halting_Lists_B
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Foundations_Halting_Arith
import Definitions.Def_MIPRE_Foundations_Repeat_Prims
import Definitions.Def_MIPRE_Foundations_Repeat_MapLoop
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit_B
import Definitions.Def_MIPRE_Foundations_Repeat_Sampler
import Definitions.Def_MIPRE_Foundations_CL_Repeat
import Definitions.Def_MIPRE_Foundations_Repeat_Bits
import Definitions.Def_MIPRE_Foundations_Cost_Machine_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineData_B
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound_B
import Definitions.Def_MIPRE_Foundations_Cost_Universal_B
import Definitions.Def_MIPRE_Foundations_Cost_Kleene_B
import Definitions.Def_MIPRE_Foundations_Repeat_DecLoop
import Definitions.Def_MIPRE_Foundations_Halting_Serial
import Definitions.Def_MIPRE_Foundations_Repeat_DecMain

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.Cost.Data
section
open Data
theorem size_list_append (l₁ l₂ : List Data) :
    (list (l₁ ++ l₂)).size + 1 = (list l₁).size + (list l₂).size := by
  induction l₁ with
  | nil => simp only [List.nil_append, list_nil, size_nil]; omega
  | cons a l ih => simp only [List.cons_append, size_list_cons] at ih ⊢; omega
end
end MIPRE.Cost.Data

namespace MIPRE.Cost.Data
section
open Data
theorem size_list_reverse (l : List Data) : (list l.reverse).size = (list l).size := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have := size_list_append l.reverse [a]
    simp only [List.reverse_cons, size_list_cons, list_nil, size_nil] at this ⊢
    omega
end
end MIPRE.Cost.Data

namespace MIPRE.Cost.Prog
section
open Data
theorem bitsBody_wellScoped : bitsBody.WellScoped 1 := by simp [bitsBody, WellScoped]
end
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
section
open Data
theorem bitsBody_stop (acc : List Data) :
    ∃ t ≤ (list acc).size + 6, Eval [Data.cons (list []) (list acc)] bitsBody (.cons .nil (list acc)) t :=
  ⟨_, by omega, Eval.elim_cons (i := 0) (n := .nil) (a := list []) (b := list acc) (by simp)
    (Eval.elim_nil (i := 0) (by simp) (Eval.cons (Eval.nil _) (Eval.var_of_get (i := 1) (v := list acc) (by simp))))⟩
end
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
section
open Data
theorem bitsBody_step (h : Data) (l acc : List Data) :
    ∃ t ≤ (list l).size + (list acc).size + h.size + 12,
      Eval [Data.cons (list (h :: l)) (list acc)] bitsBody
        (.cons (.cons .nil .nil) (.cons (list l) (list (ofBool (bitOf h) :: acc)))) t := by
  rcases h with _ | ⟨h₀, h₁⟩
  · refine ⟨_, ?_, Eval.elim_cons (i := 0) (n := .nil) (a := list (.nil :: l)) (b := list acc) (by simp)
      (Eval.elim_cons (i := 0) (a := .nil) (b := list l) (by simp)
        (Eval.elim_nil (i := 0) (by simp)
          (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _))
            (Eval.cons (Eval.var_of_get (i := 1) (v := list l) (by simp))
              (Eval.cons (Eval.nil _) (Eval.var_of_get (i := 3) (v := list acc) (by simp)))))))⟩
    simp only [size_cons, size_nil]; omega
  · refine ⟨_, ?_, Eval.elim_cons (i := 0) (n := .nil) (a := list (.cons h₀ h₁ :: l)) (b := list acc)
      (by simp)
      (Eval.elim_cons (i := 0) (a := .cons h₀ h₁) (b := list l) (by simp)
        (Eval.elim_cons (i := 0) (a := h₀) (b := h₁) (by simp)
          (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _))
            (Eval.cons (Eval.var_of_get (i := 3) (v := list l) (by simp))
              (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _))
                (Eval.var_of_get (i := 5) (v := list acc) (by simp)))))))⟩
    have := size_pos h₀
    have := size_pos h₁
    simp only [size_cons, size_nil, bitOf, ofBool]; omega
end
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
section
open Data
theorem bitsLoop_runs (l acc : List Data) (env : Env) (S : ℕ)
    (hS : (list l).size + (list acc).size + 2 * l.length ≤ S) :
    ∃ t ≤ (l.length + 1) * (S + 14),
      Eval (Data.cons (list l) (list acc) :: env) (.loop bitsBody)
        (list ((l.map fun h => ofBool (bitOf h)).reverse ++ acc)) t := by
  induction l generalizing acc with
  | nil =>
    obtain ⟨t, ht, h⟩ := bitsBody_stop acc
    refine ⟨t + 1, by simp at hS ⊢; omega, ?_⟩
    simpa using Eval.loop_stop (Eval.append_of_wellScoped h bitsBody_wellScoped env)
  | cons h l ih =>
    obtain ⟨t₁, ht₁, h₁⟩ := bitsBody_step h l acc
    have hb : (ofBool (bitOf h)).size ≤ 3 := size_ofBool _
    have hh := size_pos h
    obtain ⟨t₂, ht₂, h₂⟩ := ih (ofBool (bitOf h) :: acc) (by
      simp only [size_list_cons, List.length_cons] at hS ⊢
      omega)
    have hres : (l.map fun h => ofBool (bitOf h)).reverse ++ ofBool (bitOf h) :: acc =
        ((h :: l).map fun h => ofBool (bitOf h)).reverse ++ acc := by
      simp
    rw [hres] at h₂
    refine ⟨t₁ + t₂ + 1, ?_, Eval.loop_step (Eval.append_of_wellScoped h₁ bitsBody_wellScoped env) h₂⟩
    simp only [size_list_cons, List.length_cons] at hS ht₂ ⊢
    have : (l.length + 1 + 1) * (S + 14) = (l.length + 1) * (S + 14) + (S + 14) := by ring
    omega
end
end MIPRE.Cost.Prog

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Cost.Prog
open Data
theorem _root_.solution (l : List Data) :
    ∃ t ≤ (l.length + 2) * ((list l).size + 2 * l.length + 15) + (l.length + 2) * (4 * l.length + 20),
      bitsProg.Runs (list l) (encode (bitsOf l)) t := by
  obtain ⟨t₁, ht₁, h₁⟩ := bitsLoop_runs l [] [list l] ((list l).size + 1 + 2 * l.length) (by simp)
  set rev := (l.map fun h => ofBool (bitOf h)).reverse ++ [] with hrev
  obtain ⟨t₂, ht₂, h₂⟩ := revProg_runs rev
  have hrev' : rev.reverse = l.map fun h => ofBool (bitOf h) := by simp [hrev]
  rw [hrev'] at h₂
  have hlen : rev.length = l.length := by simp [hrev]
  have hsz : (list rev).size ≤ 4 * l.length + 1 := by
    rw [hrev, List.append_nil, size_list_reverse, ← ofList_eq_list]
    exact size_ofList_le (fun h => by cases bitOf h <;> simp [ofBool]) l
  have run : bitsProg.Runs (list l) (encode (bitsOf l)) _ :=
    Eval.let_ (Eval.cons (Eval.var_of_get (i := 0) (v := list l) (by simp)) (Eval.nil _))
      (Eval.let_ (by simpa using h₁)
        (by
          have := callVar_eval revProg_wellScoped (env := [list rev, .cons (list l) (list []), list l])
            (i := 0) (v := list rev) (by simp) h₂
          simpa [bitsOf, encode_bitStr_eq_list, List.map_map, Function.comp_def] using this))
  refine ⟨_, ?_, run⟩
  rw [hlen] at ht₂
  have h₂' : (l.length + 1 + 1) * ((list rev).size + 1 + 12) ≤ (l.length + 2) * (4 * l.length + 15) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h₁' : (l.length + 1) * ((list l).size + 1 + 2 * l.length + 14) ≤
      (l.length + 2) * ((list l).size + 2 * l.length + 15) :=
    Nat.mul_le_mul (by omega) (by omega)
  have e : (l.length + 2) * (4 * l.length + 20) =
      (l.length + 2) * (4 * l.length + 15) + 5 * l.length + 10 := by ring
  have e2 : (l.length + 2) * ((list l).size + 2 * l.length + 15) =
      (l.length + 1) * ((list l).size + 1 + 2 * l.length + 14) + ((list l).size + 2 * l.length + 15) := by
    ring
  omega
end MIPRE.Cost.Prog
