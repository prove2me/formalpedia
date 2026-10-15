-- Prove2me | solution 1 for MIPRE.Cost.Machine.getListProg_runs
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-12T16:41:48.063728+00:00
-- url     : https://prove2.me/submissions/92ce89f5-9977-4a56-88a9-02bb38b98ca2

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/Interpreter.lean (solution of MIPRE.Cost.Machine.getListProg_runs);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Computability.Primrec.List
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops
import Definitions.Def_MIPRE_Foundations_Cost_Machine
import Definitions.Def_MIPRE_Foundations_Cost_Codable
import Definitions.Def_MIPRE_Foundations_Cost_MachineData
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context; each is used only by proofs. -/
namespace MIPRE.Cost.Machine
open Prog
theorem projLeft_runs {E : Env} {i : ℕ} {d : Data} (h : E.get i = d) :
    ∃ s ≤ d.size + 2, Eval E (projLeft i) d.left s := by
  cases d with
  | nil => exact ⟨2, by simp, Eval.elim_nil (i := i) h (Eval.nil _)⟩
  | cons a b =>
    refine ⟨a.size + 1 + 1, by simp; omega, ?_⟩
    exact Eval.elim_cons (i := i) (a := a) (b := b) h (Eval.var_of_get (i := 0) (v := a) (by simp))
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Prog
theorem projRight_runs {E : Env} {i : ℕ} {d : Data} (h : E.get i = d) :
    ∃ s ≤ d.size + 2, Eval E (projRight i) d.right s := by
  cases d with
  | nil => exact ⟨2, by simp, Eval.elim_nil (i := i) h (Eval.nil _)⟩
  | cons a b =>
    refine ⟨b.size + 1 + 1, by simp; omega, ?_⟩
    exact Eval.elim_cons (i := i) (a := a) (b := b) h (Eval.var_of_get (i := 1) (v := b) (by simp))
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Prog
theorem size_right_le (d : Data) : d.right.size ≤ d.size := by cases d <;> simp; omega
end MIPRE.Cost.Machine

/-! The uploaded declaration, hoisted to the top level as `solution`. -/
open MIPRE
open MIPRE.Cost
open MIPRE.Cost.Machine
open MIPRE.Cost.Prog
theorem solution (idx env : Data) (rest : Env) :
    ∃ t ≤ (idx.size + 1) * (env.size + idx.size + 12),
      Eval (.cons env idx :: rest) getListProg (Data.getList env (Data.unaryToNat idx)) t := by
  induction idx generalizing env with
  | nil =>
    obtain ⟨s, hs, hl⟩ := projLeft_runs (E := env :: Data.nil :: Data.cons env .nil :: rest)
      (i := 0) (d := env) (by simp)
    have hbody : Eval (Data.cons env .nil :: rest) getListBody (.cons .nil env.left) _ :=
      Eval.elim_cons (i := 0) (a := env) (b := .nil) (by simp)
        (Eval.elim_nil (i := 1) (by simp) (Eval.cons (Eval.nil _) hl))
    have run := Eval.loop_stop hbody
    refine ⟨_, ?_, by simpa [getListProg, Data.getList] using run⟩
    ((try simp only [MIPRE.Cost.Data.size_cons, MIPRE.Cost.Data.size_nil, MIPRE.Cost.Data.size_ofNat, MIPRE.Cost.Machine.Frame.toData, MIPRE.Cost.Machine.Cfg.toData, MIPRE.Cost.Machine.Ctrl.toData, MIPRE.Cost.Machine.evD, MIPRE.Cost.Machine.retD, MIPRE.Cost.Prog.toData, MIPRE.Cost.Data.list_cons, MIPRE.Cost.Data.list_nil, List.map_cons, List.map_nil] at *); all_goals omega)
  | cons i₁ idx' _ ih =>
    obtain ⟨t, ht, hrun⟩ := ih env.right
    obtain ⟨s, hs, hr⟩ := projRight_runs
      (E := i₁ :: idx' :: env :: Data.cons i₁ idx' :: Data.cons env (.cons i₁ idx') :: rest)
      (i := 2) (d := env) (by simp)
    have hbody : Eval (Data.cons env (.cons i₁ idx') :: rest) getListBody
        (.cons (.cons .nil .nil) (.cons env.right idx')) _ :=
      Eval.elim_cons (i := 0) (a := env) (b := .cons i₁ idx') (by simp)
        (Eval.elim_cons (i := 1) (a := i₁) (b := idx') (by simp)
          (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _))
            (Eval.cons hr (Eval.var_of_get (i := 1) (v := idx') (by simp)))))
    have hrun' : Eval (Data.cons env.right idx' :: rest) getListProg
        (Data.getList env (Data.unaryToNat (.cons i₁ idx'))) t := by
      simpa [Data.getList, Function.iterate_succ_apply] using hrun
    have run := Eval.loop_step hbody hrun'
    refine ⟨_, ?_, by simpa [getListProg] using run⟩
    · have h1 : (Data.cons i₁ idx').size = i₁.size + idx'.size + 1 := rfl
      have h2 : env.right.size ≤ env.size := size_right_le env
      have h3 : (idx'.size + 1) * (env.right.size + idx'.size + 12) ≤
          (idx'.size + 1) * (env.size + i₁.size + idx'.size + 13) :=
        Nat.mul_le_mul_left _ (by omega)
      have h4 : (i₁.size + idx'.size + 1 + 1) * (env.size + (i₁.size + idx'.size + 1) + 12) =
          (idx'.size + 1) * (env.size + i₁.size + idx'.size + 13) +
          (i₁.size + 1) * (env.size + i₁.size + idx'.size + 13) := by ring
      have h5 : env.size + i₁.size + idx'.size + 13 ≤
          (i₁.size + 1) * (env.size + i₁.size + idx'.size + 13) :=
        Nat.le_mul_of_pos_left _ (by omega)
      rw [h1]
      omega
