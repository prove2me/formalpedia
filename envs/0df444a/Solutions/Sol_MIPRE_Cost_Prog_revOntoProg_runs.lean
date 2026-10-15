-- Prove2me | solution 1 for MIPRE.Cost.Prog.revOntoProg_runs
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-12T16:48:37.578998+00:00
-- url     : https://prove2.me/submissions/3947e469-d1ef-4e73-9baf-969d54ecfa27

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/Loops.lean (solution of MIPRE.Cost.Prog.revOntoProg_runs);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context; each is used only by proofs. -/
namespace MIPRE.Cost.Prog
theorem revOntoBody_wellScoped : revOntoBody.WellScoped 1 := by
  simp [revOntoBody, WellScoped]
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
/-- One iteration of `revOntoBody` on a non-empty list. -/
theorem revOntoBody_step (h : Data) (l acc : List Data) :
    Eval [.cons (.list (h :: l)) (.list acc)] revOntoBody
      (.cons (.cons .nil .nil) (.cons (.list l) (.list (h :: acc))))
      ((Data.list l).size + h.size + (Data.list acc).size + 11) := by
  have e := Eval.elim_cons (env := [Data.cons (.list (h :: l)) (.list acc)]) (i := 0)
    (n := .nil) (a := .list (h :: l)) (b := .list acc) (by simp)
    (Eval.elim_cons (i := 0) (n := .cons .nil (.var 1)) (a := h) (b := .list l) (by simp)
      (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _))
        (Eval.cons (Eval.var_of_get (i := 1) (v := .list l) (by simp))
          (Eval.cons (Eval.var_of_get (i := 0) (v := h) (by simp))
            (Eval.var_of_get (i := 3) (v := .list acc) (by simp))))))
  exact e.cast_cost (by omega)
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
/-- The stopping iteration of `revOntoBody` on the empty list. -/
theorem revOntoBody_stop (acc : List Data) :
    Eval [.cons (.list []) (.list acc)] revOntoBody (.cons .nil (.list acc))
      ((Data.list acc).size + 5) := by
  have e := Eval.elim_cons (env := [Data.cons (.list []) (.list acc)]) (i := 0)
    (n := .nil) (a := .list []) (b := .list acc) (by simp)
    (Eval.elim_nil (i := 0)
      (c := .cons (.cons .nil .nil) (.cons (.var 1) (.cons (.var 0) (.var 3)))) (by simp)
      (Eval.cons (Eval.nil _) (Eval.var_of_get (i := 1) (v := .list acc) (by simp))))
  exact e.cast_cost (by omega)
end MIPRE.Cost.Prog

/-! The uploaded declaration, hoisted to the top level as `solution`. -/
open MIPRE
open MIPRE.Cost
open MIPRE.Cost.Prog
theorem solution (l acc : List Data) (env : Env) (S : ℕ)
    (hS : (Data.list l).size + (Data.list acc).size ≤ S) :
    ∃ t ≤ (l.length + 1) * (S + 12),
      Eval (.cons (.list l) (.list acc) :: env) revOntoProg (.list (l.reverse ++ acc)) t := by
  induction l generalizing acc with
  | nil =>
    refine ⟨(Data.list acc).size + 5 + 1, ?_, ?_⟩
    · simp only [List.length_nil, Data.list_nil, Data.size_nil] at hS ⊢; omega
    · simpa [revOntoProg] using Eval.loop_stop
        (Eval.append_of_wellScoped (revOntoBody_stop acc) revOntoBody_wellScoped env)
  | cons h l ih =>
    have hS' : (Data.list l).size + (Data.list (h :: acc)).size ≤ S := by
      simp only [Data.size_list_cons] at hS ⊢; omega
    obtain ⟨t, ht, hrun⟩ := ih (h :: acc) hS'
    refine ⟨(Data.list l).size + h.size + (Data.list acc).size + 11 + t + 1, ?_, ?_⟩
    · simp only [Data.size_list_cons] at hS
      have h2 : (l.length + 1 + 1) * (S + 12) = (l.length + 1) * (S + 12) + (S + 12) :=
        Nat.succ_mul _ _
      simp only [List.length_cons]
      omega
    · have hstep := Eval.append_of_wellScoped (revOntoBody_step h l acc)
        revOntoBody_wellScoped env
      have := Eval.loop_step hstep hrun
      simpa [revOntoProg] using this
