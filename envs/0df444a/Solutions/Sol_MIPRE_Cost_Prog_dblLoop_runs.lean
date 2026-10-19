-- Prove2me | solution 1 for MIPRE.Cost.Prog.dblLoop_runs
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-16T15:33:58.507327+00:00
-- url     : https://prove2.me/submissions/c97bfe4e-3d10-4c81-bf60-93aa73ac581d

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Repeat/Prims.lean (solution of MIPRE.Cost.Prog.dblLoop_runs);
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
import Theorems.Thm_MIPRE_Cost_Prog_revOntoProg_runs

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.Cost.Prog
section
open Data
theorem dblBody_wellScoped : dblBody.WellScoped 1 := by
  simp [dblBody, WellScoped, revOntoProg, revOntoBody]
end
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
section
open Data
theorem dblBody_stop (a : ℕ) :
    ∃ t ≤ 2 * a + 8, Eval [Data.cons (ofNat 0) (ofNat a)] dblBody (.cons .nil (ofNat a)) t := by
  have run : Eval [Data.cons (ofNat 0) (ofNat a)] dblBody (.cons .nil (ofNat a)) _ :=
    Eval.elim_cons (env := [Data.cons (ofNat 0) (ofNat a)]) (i := 0) (n := .nil) (a := ofNat 0)
      (b := ofNat a) (by simp)
      (Eval.elim_nil (i := 0) (by simp [ofNat])
        (Eval.cons (Eval.nil _) (Eval.var_of_get (i := 1) (v := ofNat a) (by simp))))
  exact ⟨_, by simp only [size_ofNat]; omega, run⟩
end
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
section
open Data
theorem dblBody_step (m a : ℕ) :
    ∃ t ≤ (a + 1) * (4 * a + 14) + 10 * a + 2 * m + 30,
      Eval [Data.cons (ofNat (m + 1)) (ofNat a)] dblBody
        (.cons (.cons .nil .nil) (.cons (ofNat m) (ofNat (2 * a)))) t := by
  have hrev := revOntoProg_runs (List.replicate a .nil) (List.replicate a .nil)
    [.nil, ofNat m, ofNat (m + 1), ofNat a, Data.cons (ofNat (m + 1)) (ofNat a)] (4 * a + 2)
    (by rw [← ofNat_eq_list_replicate, size_ofNat]; omega)
  obtain ⟨t₁, ht₁, h₁⟩ := hrev
  have hres : Data.list ((List.replicate a Data.nil).reverse ++ List.replicate a .nil) = ofNat (2 * a) := by
    rw [List.reverse_replicate, ← List.replicate_add, ← ofNat_eq_list_replicate, Nat.two_mul]
  rw [hres, ← ofNat_eq_list_replicate] at h₁
  have run : Eval [Data.cons (ofNat (m + 1)) (ofNat a)] dblBody
      (.cons (.cons .nil .nil) (.cons (ofNat m) (ofNat (2 * a)))) _ :=
    Eval.elim_cons (env := [Data.cons (ofNat (m + 1)) (ofNat a)]) (i := 0) (n := .nil)
      (a := ofNat (m + 1)) (b := ofNat a) (by simp)
      (Eval.elim_cons (i := 0) (a := .nil) (b := ofNat m) (by simp [ofNat])
        (Eval.let_
          (Eval.let_ (Eval.cons (Eval.var_of_get (i := 3) (v := ofNat a) (by simp))
            (Eval.var_of_get (i := 3) (v := ofNat a) (by simp))) h₁)
          (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _))
            (Eval.cons (Eval.var_of_get (i := 2) (v := ofNat m) (by simp))
              (Eval.var_of_get (i := 0) (v := ofNat (2 * a)) (by simp))))))
  refine ⟨_, ?_, run⟩
  simp only [size_ofNat, List.length_replicate] at ht₁ ⊢
  have : (a + 1) * (4 * a + 2 + 12) = (a + 1) * (4 * a + 14) := by ring
  omega
end
end MIPRE.Cost.Prog

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Cost.Prog
open Data
theorem _root_.solution (m a : ℕ) (env : Env) :
    ∃ t ≤ dblCost m a,
      Eval (Data.cons (ofNat m) (ofNat a) :: env) (.loop dblBody) (ofNat (2 ^ m * a)) t := by
  induction m generalizing a with
  | zero =>
    obtain ⟨t, ht, h⟩ := dblBody_stop a
    refine ⟨t + 1, ?_, ?_⟩
    · unfold dblCost; simp only [pow_zero, one_mul]; nlinarith
    · simpa using Eval.loop_stop (Eval.append_of_wellScoped h dblBody_wellScoped env)
  | succ m ih =>
    obtain ⟨t₁, ht₁, h₁⟩ := dblBody_step m a
    obtain ⟨t₂, ht₂, h₂⟩ := ih (2 * a)
    have hres : 2 ^ m * (2 * a) = 2 ^ (m + 1) * a := by ring
    rw [hres] at h₂
    refine ⟨t₁ + t₂ + 1, ?_,
      Eval.loop_step (Eval.append_of_wellScoped h₁ dblBody_wellScoped env) h₂⟩
    unfold dblCost at ht₂ ⊢
    have hpow : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
    rw [hpow]
    have ha : a ≤ 2 ^ m * a := Nat.le_mul_of_pos_left a (pow_pos (by norm_num) m)
    have h1 : (a + 1) * (4 * a + 14) ≤ (2 * 2 ^ m * a + 1) * (4 * (2 * 2 ^ m) * a + 14) :=
      Nat.mul_le_mul (by nlinarith) (by nlinarith)
    have h2 : (2 ^ m * (2 * a) + 1) * (4 * 2 ^ m * (2 * a) + 14) + 10 * 2 ^ m * (2 * a) + 2 * m + 32 ≤
        (2 * 2 ^ m * a + 1) * (4 * (2 * 2 ^ m) * a + 14) + 10 * (2 * 2 ^ m) * a + 2 * (m + 1) + 32 := by
      have e1 : 2 ^ m * (2 * a) = 2 * 2 ^ m * a := by ring
      have e2 : 4 * 2 ^ m * (2 * a) = 4 * (2 * 2 ^ m) * a := by ring
      have e3 : 10 * 2 ^ m * (2 * a) = 10 * (2 * 2 ^ m) * a := by ring
      rw [e1, e2, e3]; omega
    have h3 : t₂ ≤ (m + 1) * ((2 * 2 ^ m * a + 1) * (4 * (2 * 2 ^ m) * a + 14) +
        10 * (2 * 2 ^ m) * a + 2 * (m + 1) + 32) := ht₂.trans (Nat.mul_le_mul_left _ h2)
    rw [Nat.succ_mul]
    nlinarith
end MIPRE.Cost.Prog
