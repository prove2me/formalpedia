-- Prove2me | solution 1 for MIPRE.Cost.Prog.pairTakeProg_runs
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-16T15:33:56.603975+00:00
-- url     : https://prove2.me/submissions/394318ac-3d74-42bc-b9c2-0859c5dc9006

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Repeat/MapLoop.lean (solution of MIPRE.Cost.Prog.pairTakeProg_runs);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Computability.Primrec.List
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Logic.Denumerable
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
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
import Theorems.Thm_MIPRE_Cost_Data_length_le_size_list_prime
import Theorems.Thm_MIPRE_Cost_Prog_takeLoop_runs

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

namespace MIPRE.Cost.Data
section
open Data
theorem size_list_take_le (s : ℕ) (l : List Data) : (list (l.take s)).size ≤ (list l).size := by
  induction l generalizing s with
  | nil => simp
  | cons a l ih =>
    cases s with
    | zero => simp only [List.take_zero, list_nil, size_nil, size_list_cons]; omega
    | succ s => simp only [List.take_succ_cons, size_list_cons]; have := ih s; omega
end
end MIPRE.Cost.Data

namespace MIPRE.Cost.Data
section
open Data
theorem size_list_drop_le (s : ℕ) (l : List Data) : (list (l.drop s)).size ≤ (list l).size := by
  induction l generalizing s with
  | nil => simp
  | cons a l ih =>
    cases s with
    | zero => exact le_rfl
    | succ s => simp only [List.drop_succ_cons, size_list_cons]; have := ih s; omega
end
end MIPRE.Cost.Data

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Cost.Prog
open Data
theorem _root_.solution (s : ℕ) (remU remY : List Data) :
    ∃ t ≤ pairTakeCost s (list remU).size (list remY).size,
      pairTakeProg.Runs (.cons (ofNat s) (.cons (list remU) (list remY)))
        (.cons (list (remU.drop s)) (.cons (list (remY.drop s))
          (.cons (list (remU.take s)) (list (remY.take s))))) t := by
  set inp : Data := .cons (ofNat s) (.cons (list remU) (list remY)) with hinp
  obtain ⟨t₁, ht₁, h₁⟩ := takeLoop_runs s remU [] [list remU, list remY, ofNat s,
    .cons (list remU) (list remY), inp]
  set tu : Data := .cons (list (remU.drop s)) (list ((remU.take s).reverse ++ [])) with htu
  obtain ⟨t₂, ht₂, h₂⟩ := takeLoop_runs s remY [] [tu, takeState s remU [], list remU, list remY,
    ofNat s, .cons (list remU) (list remY), inp]
  set ty : Data := .cons (list (remY.drop s)) (list ((remY.take s).reverse ++ [])) with hty
  obtain ⟨t₃, ht₃, h₃⟩ := revProg_runs ((remU.take s).reverse ++ [])
  obtain ⟨t₄, ht₄, h₄⟩ := revProg_runs ((remY.take s).reverse ++ [])
  have e₃ : ((remU.take s).reverse ++ []).reverse = remU.take s := by simp
  have e₄ : ((remY.take s).reverse ++ []).reverse = remY.take s := by simp
  rw [e₃] at h₃
  rw [e₄] at h₄
  have run : Eval [inp] pairTakeProg (.cons (list (remU.drop s)) (.cons (list (remY.drop s))
      (.cons (list (remU.take s)) (list (remY.take s))))) _ :=
    Eval.elim_cons (env := [inp]) (i := 0) (n := .nil) (a := ofNat s)
      (b := .cons (list remU) (list remY)) (by simp [hinp])
      (Eval.elim_cons (i := 1) (n := .nil) (a := list remU) (b := list remY) (by simp)
        (Eval.let_ (Eval.cons (Eval.var_of_get (i := 2) (v := ofNat s) (by simp))
            (Eval.cons (Eval.var_of_get (i := 0) (v := list remU) (by simp)) (Eval.nil _)))
          (Eval.let_ h₁
            (Eval.let_ (Eval.cons (Eval.var_of_get (i := 4) (v := ofNat s) (by simp))
                (Eval.cons (Eval.var_of_get (i := 3) (v := list remY) (by simp)) (Eval.nil _)))
              (Eval.let_ h₂
                (Eval.elim_cons (i := 2) (n := .nil) (a := list (remU.drop s))
                  (b := list ((remU.take s).reverse ++ [])) (by simp [htu])
                  (Eval.elim_cons (i := 2) (n := .nil) (a := list (remY.drop s))
                    (b := list ((remY.take s).reverse ++ [])) (by simp [hty])
                    (Eval.let_ (callVar_eval revProg_wellScoped (i := 3)
                        (v := list ((remU.take s).reverse ++ [])) (by simp) h₃)
                      (Eval.let_ (callVar_eval revProg_wellScoped (i := 2)
                          (v := list ((remY.take s).reverse ++ [])) (by simp) h₄)
                        (Eval.cons (Eval.var_of_get (i := 4) (v := list (remU.drop s)) (by simp))
                          (Eval.cons (Eval.var_of_get (i := 2) (v := list (remY.drop s)) (by simp))
                            (Eval.cons (Eval.var_of_get (i := 1) (v := list (remU.take s)) (by simp))
                              (Eval.var_of_get (i := 0) (v := list (remY.take s)) (by simp))))))))))))))
  refine ⟨_, ?_, run⟩
  simp only [size_ofNat, List.append_nil, size_list_reverse, list_nil, size_nil,
    List.length_reverse] at ht₁ ht₂ ht₃ ht₄ ⊢
  have hU : (list (remU.take s)).size ≤ (list remU).size := size_list_take_le s remU
  have hY : (list (remY.take s)).size ≤ (list remY).size := size_list_take_le s remY
  have hU' : (list (remU.drop s)).size ≤ (list remU).size := size_list_drop_le s remU
  have hY' : (list (remY.drop s)).size ≤ (list remY).size := size_list_drop_le s remY
  have hlU : (remU.take s).length + 1 ≤ (list (remU.take s)).size := length_le_size_list_prime _
  have hlY : (remY.take s).length + 1 ≤ (list (remY.take s)).size := length_le_size_list_prime _
  have h₃' : ((remU.take s).length + 1 + 1) * ((list (remU.take s)).size + 1 + 12) ≤
      ((list remU).size + 2) * ((list remU).size + 13) := Nat.mul_le_mul (by omega) (by omega)
  have h₄' : ((remY.take s).length + 1 + 1) * ((list (remY.take s)).size + 1 + 12) ≤
      ((list remY).size + 2) * ((list remY).size + 13) := Nat.mul_le_mul (by omega) (by omega)
  have h₁' : (s + 1) * ((list remU).size + 1 + 2 * s + 20) ≤
      (s + 1) * ((list remU).size + (list remY).size + 2 * s + 21) :=
    Nat.mul_le_mul_left _ (by omega)
  have h₂' : (s + 1) * ((list remY).size + 1 + 2 * s + 20) ≤
      (s + 1) * ((list remU).size + (list remY).size + 2 * s + 21) :=
    Nat.mul_le_mul_left _ (by omega)
  have h₃'' : ((list remU).size + 2) * ((list remU).size + 13) ≤
      ((list remU).size + 2) * ((list remU).size + (list remY).size + 13) :=
    Nat.mul_le_mul_left _ (by omega)
  have h₄'' : ((list remY).size + 2) * ((list remY).size + 13) ≤
      ((list remY).size + 2) * ((list remU).size + (list remY).size + 13) :=
    Nat.mul_le_mul_left _ (by omega)
  unfold pairTakeCost
  omega
end MIPRE.Cost.Prog
