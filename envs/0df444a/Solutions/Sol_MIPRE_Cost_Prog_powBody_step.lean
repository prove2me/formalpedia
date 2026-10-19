-- Prove2me | solution 1 for MIPRE.Cost.Prog.powBody_step
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-16T15:33:03.10185+00:00
-- url     : https://prove2.me/submissions/2e0e945d-8942-46b2-bffb-444182867742

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Repeat/Prims.lean (solution of MIPRE.Cost.Prog.powBody_step);
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
/-- The size of a list of `m` copies of `nil` in front of `acc`. -/
theorem size_list_replicate_nil_append (m : ℕ) (acc : List Data) :
    (Data.list (List.replicate m .nil ++ acc)).size = 2 * m + (Data.list acc).size := by
  induction m with
  | zero => simp
  | succ m ih => rw [List.replicate_succ, List.cons_append, Data.size_list_cons, ih]; simp; omega
end
end MIPRE.Cost.Prog

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Cost.Prog
open Data
theorem _root_.solution (e : ℕ) (bl bn acc : List Data) :
    ∃ t ≤ (bn.length + 1) * ((Data.list bl).size + (Data.list bn).size + (Data.list acc).size +
        2 * bn.length + 13) +
      (bl.length + 1) * ((Data.list bl).size + (Data.list bn).size + (Data.list acc).size +
        2 * bn.length + 2 * bl.length + 13) +
      4 * ((Data.list bl).size + (Data.list bn).size + (Data.list acc).size + 2 * e + 2 * bn.length +
        2 * bl.length) + 40,
      Eval [powState (e + 1) bl bn acc] powBody
        (.cons (.cons .nil .nil)
          (powState e bl bn (List.replicate (bl.length + bn.length) .nil ++ acc))) t := by
  set r' : Data := .cons (.list bn) (.list acc) with hr'
  set r : Data := .cons (.list bl) r' with hr
  set st : Data := powState (e + 1) bl bn acc with hst
  have hS₁ : (Data.list bn).size + (Data.list acc).size + 2 * bn.length ≤
      (Data.list bl).size + (Data.list bn).size + (Data.list acc).size + 2 * bn.length := by omega
  obtain ⟨t₁, ht₁, h₁⟩ := lenLoop_runs bn acc
    [.list bn, .list acc, .list bl, r', .nil, ofNat e, ofNat (e + 1), r, st] _ hS₁
  set acc₁ : List Data := List.replicate bn.length .nil ++ acc with hacc₁
  have hsz₁ : (Data.list acc₁).size = 2 * bn.length + (Data.list acc).size :=
    size_list_replicate_nil_append _ _
  have hS₂ : (Data.list bl).size + (Data.list acc₁).size + 2 * bl.length ≤
      (Data.list bl).size + (Data.list bn).size + (Data.list acc).size + 2 * bn.length +
        2 * bl.length := by rw [hsz₁]; omega
  obtain ⟨t₂, ht₂, h₂⟩ := lenLoop_runs bl acc₁
    [.list acc₁, .list bn, .list acc, .list bl, r', .nil, ofNat e, ofNat (e + 1), r, st] _ hS₂
  have hfin : List.replicate bl.length .nil ++ acc₁ =
      List.replicate (bl.length + bn.length) .nil ++ acc := by
    rw [hacc₁, ← List.append_assoc, ← List.replicate_add]
  rw [hfin] at h₂
  set acc₂ : List Data := List.replicate (bl.length + bn.length) .nil ++ acc with hacc₂
  have hsz₂ : (Data.list acc₂).size = 2 * (bl.length + bn.length) + (Data.list acc).size :=
    size_list_replicate_nil_append _ _
  have run : Eval [st] powBody (.cons (.cons .nil .nil) (powState e bl bn acc₂)) _ :=
    Eval.elim_cons (env := [st]) (i := 0) (n := .nil) (a := ofNat (e + 1)) (b := r)
      (by simp [hst, powState, hr, hr'])
      (Eval.elim_cons (i := 0) (a := .nil) (b := ofNat e) (by simp [ofNat])
        (Eval.elim_cons (i := 3) (n := .nil) (a := .list bl) (b := r') (by simp [hr])
          (Eval.elim_cons (i := 1) (n := .nil) (a := .list bn) (b := .list acc) (by simp [hr'])
            (Eval.let_
              (Eval.let_ (Eval.cons (Eval.var_of_get (i := 0) (v := .list bn) (by simp))
                (Eval.var_of_get (i := 1) (v := .list acc) (by simp))) h₁)
              (Eval.let_
                (Eval.let_ (Eval.cons (Eval.var_of_get (i := 3) (v := .list bl) (by simp))
                  (Eval.var_of_get (i := 0) (v := .list acc₁) (by simp))) h₂)
                (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _))
                  (Eval.cons (Eval.var_of_get (i := 7) (v := ofNat e) (by simp))
                    (Eval.cons (Eval.var_of_get (i := 4) (v := .list bl) (by simp))
                      (Eval.cons (Eval.var_of_get (i := 2) (v := .list bn) (by simp))
                        (Eval.var_of_get (i := 0) (v := .list acc₂) (by simp)))))))))))
  refine ⟨_, ?_, run⟩
  simp only [size_ofNat, hsz₁, hsz₂]
  omega
end MIPRE.Cost.Prog
