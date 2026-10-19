-- Prove2me | solution 1 for MIPRE.Cost.Prog.takeLoop_runs
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-16T15:32:44.175168+00:00
-- url     : https://prove2.me/submissions/480d7e51-8dd2-4876-aa14-a2385b96c45b

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Repeat/Prims.lean (solution of MIPRE.Cost.Prog.takeLoop_runs);
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

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.Cost.Prog
section
open Data
theorem takeBody_wellScoped : takeBody.WellScoped 1 := by
  simp [takeBody, WellScoped]
end
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
section
open Data
theorem takeBody_stop_counter (rem cur : List Data) :
    ∃ t ≤ (Data.list rem).size + (Data.list cur).size + 8,
      Eval [takeState 0 rem cur] takeBody (.cons .nil (.cons (.list rem) (.list cur))) t := by
  have run : Eval [takeState 0 rem cur] takeBody (.cons .nil (.cons (.list rem) (.list cur))) _ :=
    Eval.elim_cons (env := [takeState 0 rem cur]) (i := 0) (n := .nil) (a := ofNat 0)
      (b := .cons (.list rem) (.list cur)) (by simp [takeState])
      (Eval.elim_nil (i := 0) (by simp [ofNat])
        (Eval.cons (Eval.nil _)
          (Eval.var_of_get (i := 1) (v := .cons (.list rem) (.list cur)) (by simp))))
  exact ⟨_, by simp only [Data.size_cons]; omega, run⟩
end
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
section
open Data
theorem takeBody_stop_empty (c : ℕ) (cur : List Data) :
    ∃ t ≤ (Data.list cur).size + 2 * c + 12,
      Eval [takeState (c + 1) [] cur] takeBody (.cons .nil (.cons (.list []) (.list cur))) t := by
  have run : Eval [takeState (c + 1) [] cur] takeBody (.cons .nil (.cons (.list []) (.list cur))) _ :=
    Eval.elim_cons (env := [takeState (c + 1) [] cur]) (i := 0) (n := .nil) (a := ofNat (c + 1))
      (b := .cons (.list []) (.list cur)) (by simp [takeState])
      (Eval.elim_cons (i := 0) (a := .nil) (b := ofNat c) (by simp [ofNat])
        (Eval.elim_cons (i := 3) (n := .nil) (a := .list []) (b := .list cur) (by simp)
          (Eval.elim_nil (i := 0) (by simp)
            (Eval.cons (Eval.nil _) (Eval.cons (Eval.nil _)
              (Eval.var_of_get (i := 1) (v := .list cur) (by simp)))))))
  exact ⟨_, by omega, run⟩
end
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
section
open Data
theorem takeBody_step (c : ℕ) (h : Data) (rem cur : List Data) :
    ∃ t ≤ (Data.list rem).size + h.size + (Data.list cur).size + 2 * c + 18,
      Eval [takeState (c + 1) (h :: rem) cur] takeBody
        (.cons (.cons .nil .nil) (takeState c rem (h :: cur))) t := by
  have run : Eval [takeState (c + 1) (h :: rem) cur] takeBody
      (.cons (.cons .nil .nil) (takeState c rem (h :: cur))) _ :=
    Eval.elim_cons (env := [takeState (c + 1) (h :: rem) cur]) (i := 0) (n := .nil)
      (a := ofNat (c + 1)) (b := .cons (.list (h :: rem)) (.list cur)) (by simp [takeState])
      (Eval.elim_cons (i := 0) (a := .nil) (b := ofNat c) (by simp [ofNat])
        (Eval.elim_cons (i := 3) (n := .nil) (a := .list (h :: rem)) (b := .list cur) (by simp)
          (Eval.elim_cons (i := 0) (a := h) (b := .list rem) (by simp)
            (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _))
              (Eval.cons (Eval.var_of_get (i := 5) (v := ofNat c) (by simp))
                (Eval.cons (Eval.var_of_get (i := 1) (v := .list rem) (by simp))
                  (Eval.cons (Eval.var_of_get (i := 0) (v := h) (by simp))
                    (Eval.var_of_get (i := 3) (v := .list cur) (by simp)))))))))
  exact ⟨_, by simp only [size_ofNat]; omega, run⟩
end
end MIPRE.Cost.Prog

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Cost.Prog
open Data
theorem _root_.solution (c : ℕ) (rem cur : List Data) (env : Env) :
    ∃ t ≤ (c + 1) * ((Data.list rem).size + (Data.list cur).size + 2 * c + 20),
      Eval (takeState c rem cur :: env) (.loop takeBody)
        (.cons (.list (rem.drop c)) (.list ((rem.take c).reverse ++ cur))) t := by
  induction c generalizing rem cur with
  | zero =>
    obtain ⟨t, ht, h⟩ := takeBody_stop_counter rem cur
    refine ⟨t + 1, by omega, ?_⟩
    simpa using Eval.loop_stop (Eval.append_of_wellScoped h takeBody_wellScoped env)
  | succ c ih =>
    cases rem with
    | nil =>
      obtain ⟨t, ht, h⟩ := takeBody_stop_empty c cur
      refine ⟨t + 1, ?_, ?_⟩
      · simp only [Data.list_nil, Data.size_nil] at ht ⊢; nlinarith
      · simpa using Eval.loop_stop (Eval.append_of_wellScoped h takeBody_wellScoped env)
    | cons h rem =>
      obtain ⟨t₁, ht₁, h₁⟩ := takeBody_step c h rem cur
      obtain ⟨t₂, ht₂, h₂⟩ := ih rem (h :: cur)
      have hres : (rem.take c).reverse ++ (h :: cur) = ((h :: rem).take (c + 1)).reverse ++ cur := by
        simp [List.take_succ_cons, List.reverse_cons]
      rw [hres] at h₂
      refine ⟨t₁ + t₂ + 1, ?_,
        Eval.loop_step (Eval.append_of_wellScoped h₁ takeBody_wellScoped env) h₂⟩
      simp only [Data.size_list_cons] at ht₁ ht₂ ⊢
      have := Nat.succ_mul (c + 1) ((h.size + (Data.list rem).size + 1) + (Data.list cur).size + 2 * (c + 1) + 20)
      nlinarith
end MIPRE.Cost.Prog
