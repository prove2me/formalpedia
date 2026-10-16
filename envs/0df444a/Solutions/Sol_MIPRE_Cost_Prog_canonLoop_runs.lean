-- Prove2me | solution 1 for MIPRE.Cost.Prog.canonLoop_runs
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-15T20:17:18.752439+00:00
-- url     : https://prove2.me/submissions/4799607e-9e65-4b1a-b95c-6ac248d3ffb0

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Halting/Lists.lean (solution of MIPRE.Cost.Prog.canonLoop_runs);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Computability.Primrec.List
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Logic.Denumerable
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Codable
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Halting_Descriptions
import Definitions.Def_MIPRE_Foundations_Cost_Numeric
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Halting_Lists

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.Cost.Prog
open Data
theorem canonBody_wellScoped : canonBody.WellScoped 1 := by
  simp [canonBody, WellScoped]
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
open Data
theorem canonBody_nil (last : Data) :
    ∃ t ≤ last.size + 20, Eval [Data.cons Data.nil last] canonBody (Data.cons Data.nil last) t := by
  refine ⟨_, ?_, Eval.elim_cons (i := 0) (a := Data.nil) (b := last) (by simp)
    (Eval.elim_nil (i := 0) (by simp)
    (Eval.cons (Eval.nil _) (Eval.var_of_get (i := 1) (v := last) (by simp))))⟩
  ((try simp only [MIPRE.Cost.Data.size_cons, MIPRE.Cost.Data.size_nil, MIPRE.Cost.encode_bool, MIPRE.Cost.Data.ofBool]) <;> omega)
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
open Data
theorem canonBody_step (h r last : Data) :
    ∃ t ≤ r.size + 20,
      Eval [Data.cons (Data.cons h r) last] canonBody
        (match h with
          | Data.nil => Data.cons (Data.cons Data.nil Data.nil) (Data.cons r Data.nil)
          | Data.cons Data.nil Data.nil =>
              Data.cons (Data.cons Data.nil Data.nil) (Data.cons r (Data.cons Data.nil Data.nil))
          | _ => Data.cons Data.nil Data.nil) t := by
  rcases h with _ | ⟨_ | ⟨a1, a2⟩, _ | ⟨b1, b2⟩⟩
  · refine ⟨_, ?_, Eval.elim_cons (i := 0) (a := Data.cons Data.nil r) (b := last) (by simp)
      (Eval.elim_cons (i := 0) (a := Data.nil) (b := r) (by simp)
      (Eval.elim_nil (i := 0) (by simp)
      (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _)) (Eval.cons (Eval.var_of_get (i := 1) (v := r) (by simp)) (Eval.nil _)))))⟩
    ((try simp only [MIPRE.Cost.Data.size_cons, MIPRE.Cost.Data.size_nil, MIPRE.Cost.encode_bool, MIPRE.Cost.Data.ofBool]) <;> omega)
  · refine ⟨_, ?_, Eval.elim_cons (i := 0) (a := Data.cons (Data.cons Data.nil Data.nil) r) (b := last) (by simp)
      (Eval.elim_cons (i := 0) (a := Data.cons Data.nil Data.nil) (b := r) (by simp)
      (Eval.elim_cons (i := 0) (a := Data.nil) (b := Data.nil) (by simp)
      (Eval.elim_nil (i := 0) (by simp)
      (Eval.elim_nil (i := 1) (by simp)
      (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _)) (Eval.cons (Eval.var_of_get (i := 3) (v := r) (by simp)) (Eval.cons (Eval.nil _) (Eval.nil _))))))))⟩
    ((try simp only [MIPRE.Cost.Data.size_cons, MIPRE.Cost.Data.size_nil, MIPRE.Cost.encode_bool, MIPRE.Cost.Data.ofBool]) <;> omega)
  · refine ⟨_, ?_, Eval.elim_cons (i := 0) (a := Data.cons (Data.cons Data.nil (Data.cons b1 b2)) r) (b := last) (by simp)
      (Eval.elim_cons (i := 0) (a := Data.cons Data.nil (Data.cons b1 b2)) (b := r) (by simp)
      (Eval.elim_cons (i := 0) (a := Data.nil) (b := Data.cons b1 b2) (by simp)
      (Eval.elim_nil (i := 0) (by simp)
      (Eval.elim_cons (i := 1) (a := b1) (b := b2) (by simp)
      (Eval.cons (Eval.nil _) (Eval.nil _))))))⟩
    ((try simp only [MIPRE.Cost.Data.size_cons, MIPRE.Cost.Data.size_nil, MIPRE.Cost.encode_bool, MIPRE.Cost.Data.ofBool]) <;> omega)
  · refine ⟨_, ?_, Eval.elim_cons (i := 0) (a := Data.cons (Data.cons (Data.cons a1 a2) Data.nil) r) (b := last) (by simp)
      (Eval.elim_cons (i := 0) (a := Data.cons (Data.cons a1 a2) Data.nil) (b := r) (by simp)
      (Eval.elim_cons (i := 0) (a := Data.cons a1 a2) (b := Data.nil) (by simp)
      (Eval.elim_cons (i := 0) (a := a1) (b := a2) (by simp)
      (Eval.cons (Eval.nil _) (Eval.nil _)))))⟩
    ((try simp only [MIPRE.Cost.Data.size_cons, MIPRE.Cost.Data.size_nil, MIPRE.Cost.encode_bool, MIPRE.Cost.Data.ofBool]) <;> omega)
  · refine ⟨_, ?_, Eval.elim_cons (i := 0) (a := Data.cons (Data.cons (Data.cons a1 a2) (Data.cons b1 b2)) r) (b := last) (by simp)
      (Eval.elim_cons (i := 0) (a := Data.cons (Data.cons a1 a2) (Data.cons b1 b2)) (b := r) (by simp)
      (Eval.elim_cons (i := 0) (a := Data.cons a1 a2) (b := Data.cons b1 b2) (by simp)
      (Eval.elim_cons (i := 0) (a := a1) (b := a2) (by simp)
      (Eval.cons (Eval.nil _) (Eval.nil _)))))⟩
    ((try simp only [MIPRE.Cost.Data.size_cons, MIPRE.Cost.Data.size_nil, MIPRE.Cost.encode_bool, MIPRE.Cost.Data.ofBool]) <;> omega)
end MIPRE.Cost.Prog

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Cost.Prog
open Data
theorem _root_.solution (d : Data) (last : Bool) (env : Env) (S : ℕ) (hS : d.size + 3 ≤ S) :
    ∃ t ≤ (d.spine + 1) * (S + 21),
      Eval (Data.cons d (encode last) :: env) (.loop canonBody) (encode (canonWalk d last)) t := by
  induction d generalizing last with
  | nil =>
    obtain ⟨t, ht, hrun⟩ := canonBody_nil (encode last)
    have hstop := Eval.loop_stop (Eval.append_of_wellScoped hrun canonBody_wellScoped env)
    refine ⟨t + 1, ?_, by simpa [canonWalk] using hstop⟩
    have : (encode last : Data).size ≤ 3 := by cases last <;> simp [encode_bool, ofBool]
    simp only [spine_nil, size_nil] at hS ⊢
    omega
  | cons h r _ ih =>
    obtain ⟨t, ht, hrun⟩ := canonBody_step h r (encode last)
    have hS' : r.size + 3 ≤ S := by simp only [size_cons] at hS; have := size_pos h; omega
    have hle : S + 21 ≤ (spine (Data.cons h r) + 1) * (S + 21) :=
      Nat.le_mul_of_pos_left _ (by omega)
    have h2 : (spine (Data.cons h r) + 1) * (S + 21) = (r.spine + 1) * (S + 21) + (S + 21) := by
      simp only [spine_cons]; ring
    rcases h with _ | ⟨_ | ⟨a1, a2⟩, _ | ⟨b1, b2⟩⟩
    · obtain ⟨t', ht', hrun'⟩ := ih false hS'
      refine ⟨t + t' + 1, by simp only [size_cons] at hS; omega, ?_⟩
      have := Eval.loop_step (Eval.append_of_wellScoped hrun canonBody_wellScoped env)
        (by simpa [encode_bool] using hrun')
      simpa [canonWalk, encode_bool] using this
    · obtain ⟨t', ht', hrun'⟩ := ih true hS'
      refine ⟨t + t' + 1, by simp only [size_cons] at hS; omega, ?_⟩
      have := Eval.loop_step (Eval.append_of_wellScoped hrun canonBody_wellScoped env)
        (by simpa [encode_bool] using hrun')
      simpa [canonWalk, encode_bool] using this
    all_goals
      refine ⟨t + 1, by simp only [size_cons] at hS; omega, ?_⟩
      have := Eval.loop_stop (Eval.append_of_wellScoped hrun canonBody_wellScoped env)
      simpa [canonWalk, encode_bool, ofBool] using this
end MIPRE.Cost.Prog
