-- Prove2me | solution 1 for MIPRE.Cost.Prog.bitWalkProg_runs
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-16T15:29:35.940167+00:00
-- url     : https://prove2.me/submissions/04111e1d-f8c6-4f28-91ac-225fc61947a1

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Halting/Lists.lean (solution of MIPRE.Cost.Prog.bitWalkProg_runs);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Computability.Primrec.List
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Logic.Denumerable
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

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.Cost.Data
section
theorem isBit_iff (d : Data) : isBit d = true ↔ ∃ b, d = ofBool b := by
  rcases d with _ | ⟨_ | ⟨a, b⟩, _ | ⟨c, e⟩⟩ <;> simp [isBit, ofBool]
end
end MIPRE.Cost.Data

namespace MIPRE.Cost.Prog
section
open Data
theorem bitWalkBody_wellScoped : bitWalkBody.WellScoped 1 := by
  simp [bitWalkBody, WellScoped]
end
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
section
open Data
theorem bitWalkBody_lnil (u : Data) :
    ∃ t ≤ u.size + 20, Eval [Data.cons Data.nil u] bitWalkBody (Data.cons Data.nil (Data.cons Data.nil u)) t := by
  refine ⟨_, ?_, Eval.elim_cons (i := 0) (a := Data.nil) (b := u) (by simp)
    (Eval.elim_nil (i := 0) (by simp)
    (Eval.cons (Eval.nil _) (Eval.cons (Eval.nil _) (Eval.var_of_get (i := 1) (v := u) (by simp)))))⟩
  ((try simp only [MIPRE.Cost.Data.size_cons, MIPRE.Cost.Data.size_nil, MIPRE.Cost.encode_bool, MIPRE.Cost.Data.ofBool]) <;> omega)
end
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
section
open Data
theorem bitWalkBody_unil (h l' : Data) :
    ∃ t ≤ (Data.cons h l').size + 20, Eval [Data.cons (Data.cons h l') Data.nil] bitWalkBody (Data.cons Data.nil (Data.cons (Data.cons h l') Data.nil)) t := by
  refine ⟨_, ?_, Eval.elim_cons (i := 0) (a := Data.cons h l') (b := Data.nil) (by simp)
    (Eval.elim_cons (i := 0) (a := h) (b := l') (by simp)
    (Eval.elim_nil (i := 3) (by simp)
    (Eval.cons (Eval.nil _) (Eval.cons (Eval.var_of_get (i := 2) (v := Data.cons h l') (by simp)) (Eval.nil _)))))⟩
  ((try simp only [MIPRE.Cost.Data.size_cons, MIPRE.Cost.Data.size_nil, MIPRE.Cost.encode_bool, MIPRE.Cost.Data.ofBool]) <;> omega)
end
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
section
open Data
theorem bitWalkBody_step (h l' c u' : Data) (hb : isBit h = true) :
    ∃ t ≤ l'.size + u'.size + 20,
      Eval [Data.cons (Data.cons h l') (Data.cons c u')] bitWalkBody
        (Data.cons (Data.cons Data.nil Data.nil) (Data.cons l' u')) t := by
  obtain ⟨b, rfl⟩ := (isBit_iff h).1 hb
  cases b
  · refine ⟨_, ?_, Eval.elim_cons (i := 0) (a := Data.cons (ofBool false) l') (b := Data.cons c u') (by simp)
      (Eval.elim_cons (i := 0) (a := ofBool false) (b := l') (by simp)
      (Eval.elim_cons (i := 3) (a := c) (b := u') (by simp)
      (Eval.elim_nil (i := 2) (by simp [ofBool])
      (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _)) (Eval.cons (Eval.var_of_get (i := 3) (v := l') (by simp)) (Eval.var_of_get (i := 1) (v := u') (by simp)))))))⟩
    ((try simp only [MIPRE.Cost.Data.size_cons, MIPRE.Cost.Data.size_nil, MIPRE.Cost.encode_bool, MIPRE.Cost.Data.ofBool]) <;> omega)
  · refine ⟨_, ?_, Eval.elim_cons (i := 0) (a := Data.cons (ofBool true) l') (b := Data.cons c u') (by simp)
      (Eval.elim_cons (i := 0) (a := ofBool true) (b := l') (by simp)
      (Eval.elim_cons (i := 3) (a := c) (b := u') (by simp)
      (Eval.elim_cons (i := 2) (a := Data.nil) (b := Data.nil) (by simp [ofBool])
      (Eval.elim_nil (i := 0) (by simp)
      (Eval.elim_nil (i := 1) (by simp)
      (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _)) (Eval.cons (Eval.var_of_get (i := 5) (v := l') (by simp)) (Eval.var_of_get (i := 3) (v := u') (by simp)))))))))⟩
    ((try simp only [MIPRE.Cost.Data.size_cons, MIPRE.Cost.Data.size_nil, MIPRE.Cost.encode_bool, MIPRE.Cost.Data.ofBool]) <;> omega)
end
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
section
open Data
theorem bitWalkBody_fail (h l' c u' : Data) (hb : isBit h = false) :
    ∃ t ≤ 20, Eval [Data.cons (Data.cons h l') (Data.cons c u')] bitWalkBody
      (Data.cons Data.nil Data.nil) t := by
  rcases h with _ | ⟨_ | ⟨a1, a2⟩, _ | ⟨b1, b2⟩⟩
  · simp [isBit] at hb
  · simp [isBit] at hb
  · refine ⟨_, ?_, Eval.elim_cons (i := 0) (a := Data.cons (Data.cons Data.nil (Data.cons b1 b2)) l') (b := Data.cons c u') (by simp)
      (Eval.elim_cons (i := 0) (a := Data.cons Data.nil (Data.cons b1 b2)) (b := l') (by simp)
      (Eval.elim_cons (i := 3) (a := c) (b := u') (by simp)
      (Eval.elim_cons (i := 2) (a := Data.nil) (b := Data.cons b1 b2) (by simp)
      (Eval.elim_nil (i := 0) (by simp)
      (Eval.elim_cons (i := 1) (a := b1) (b := b2) (by simp)
      ((Eval.cons (Eval.nil _) (Eval.nil _))))))))⟩
    ((try simp only [MIPRE.Cost.Data.size_cons, MIPRE.Cost.Data.size_nil, MIPRE.Cost.encode_bool, MIPRE.Cost.Data.ofBool]) <;> omega)
  · refine ⟨_, ?_, Eval.elim_cons (i := 0) (a := Data.cons (Data.cons (Data.cons a1 a2) Data.nil) l') (b := Data.cons c u') (by simp)
      (Eval.elim_cons (i := 0) (a := Data.cons (Data.cons a1 a2) Data.nil) (b := l') (by simp)
      (Eval.elim_cons (i := 3) (a := c) (b := u') (by simp)
      (Eval.elim_cons (i := 2) (a := Data.cons a1 a2) (b := Data.nil) (by simp)
      (Eval.elim_cons (i := 0) (a := a1) (b := a2) (by simp)
      ((Eval.cons (Eval.nil _) (Eval.nil _)))))))⟩
    ((try simp only [MIPRE.Cost.Data.size_cons, MIPRE.Cost.Data.size_nil, MIPRE.Cost.encode_bool, MIPRE.Cost.Data.ofBool]) <;> omega)
  · refine ⟨_, ?_, Eval.elim_cons (i := 0) (a := Data.cons (Data.cons (Data.cons a1 a2) (Data.cons b1 b2)) l') (b := Data.cons c u') (by simp)
      (Eval.elim_cons (i := 0) (a := Data.cons (Data.cons a1 a2) (Data.cons b1 b2)) (b := l') (by simp)
      (Eval.elim_cons (i := 3) (a := c) (b := u') (by simp)
      (Eval.elim_cons (i := 2) (a := Data.cons a1 a2) (b := Data.cons b1 b2) (by simp)
      (Eval.elim_cons (i := 0) (a := a1) (b := a2) (by simp)
      ((Eval.cons (Eval.nil _) (Eval.nil _)))))))⟩
    ((try simp only [MIPRE.Cost.Data.size_cons, MIPRE.Cost.Data.size_nil, MIPRE.Cost.encode_bool, MIPRE.Cost.Data.ofBool]) <;> omega)
end
end MIPRE.Cost.Prog

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Cost.Prog
open Data
theorem _root_.solution (l u : Data) (env : Env) (S : ℕ) (hS : l.size + u.size ≤ S) :
    ∃ t ≤ (u.spine + 1) * (S + 21),
      Eval (Data.cons l u :: env) bitWalkProg (bitWalk l u) t := by
  induction l generalizing u with
  | nil =>
    obtain ⟨t, ht, hrun⟩ := bitWalkBody_lnil u
    have hstop := Eval.loop_stop (Eval.append_of_wellScoped hrun bitWalkBody_wellScoped env)
    refine ⟨t + 1, ?_, by simpa [bitWalk, bitWalkProg] using hstop⟩
    have : S + 21 ≤ (u.spine + 1) * (S + 21) := Nat.le_mul_of_pos_left _ (by omega)
    omega
  | cons h l' _ ih =>
    cases u with
    | nil =>
      obtain ⟨t, ht, hrun⟩ := bitWalkBody_unil h l'
      have hstop := Eval.loop_stop (Eval.append_of_wellScoped hrun bitWalkBody_wellScoped env)
      refine ⟨t + 1, ?_, by simpa [bitWalk, bitWalkProg] using hstop⟩
      simp only [spine_nil, size_cons] at hS ht ⊢
      omega
    | cons c u' =>
      rcases hb : isBit h
      · obtain ⟨t, ht, hrun⟩ := bitWalkBody_fail h l' c u' hb
        have hstop := Eval.loop_stop (Eval.append_of_wellScoped hrun bitWalkBody_wellScoped env)
        refine ⟨t + 1, ?_, by simpa [bitWalk, hb, bitWalkProg] using hstop⟩
        have : S + 21 ≤ (spine (Data.cons c u') + 1) * (S + 21) :=
          Nat.le_mul_of_pos_left _ (by omega)
        omega
      · obtain ⟨t, ht, hrun⟩ := bitWalkBody_step h l' c u' hb
        have hS' : l'.size + u'.size ≤ S := by
          simp only [size_cons] at hS; have := size_pos h; have := size_pos c; omega
        obtain ⟨t', ht', hrun'⟩ := ih u' hS'
        refine ⟨t + t' + 1, ?_, ?_⟩
        · have h2 : (spine (Data.cons c u') + 1) * (S + 21) =
              (u'.spine + 1) * (S + 21) + (S + 21) := by
            simp only [spine_cons]; ring
          simp only [size_cons] at hS
          omega
        · have := Eval.loop_step (Eval.append_of_wellScoped hrun bitWalkBody_wellScoped env) hrun'
          simpa [bitWalk, hb, bitWalkProg] using this
end MIPRE.Cost.Prog
