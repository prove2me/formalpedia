-- Prove2me | solution 1 for MIPRE.Cost.Machine.stepCostProg_ev
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-12T16:54:57.57868+00:00
-- url     : https://prove2.me/submissions/e00738e7-9b12-4d84-9ffb-3631b2da26b6

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/Universal.lean (solution of MIPRE.Cost.Machine.stepCostProg_ev);
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
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit
import Definitions.Def_MIPRE_Foundations_Cost_Machine
import Definitions.Def_MIPRE_Foundations_Cost_Codable
import Definitions.Def_MIPRE_Foundations_Cost_MachineData
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound
import Definitions.Def_MIPRE_Foundations_Cost_Universal
import Theorems.Thm_MIPRE_Cost_Machine_dispatch_runs

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
theorem getListBody_wellScoped : getListBody.WellScoped 1 := by
  simp [getListBody, projLeft, projRight, WellScoped]
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Prog
theorem getListProg_wellScoped : getListProg.WellScoped 1 :=
  ⟨Nat.zero_lt_one, getListBody_wellScoped⟩
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Polynomial
open Prog
theorem costVar_wellScoped : costVar.WellScoped 1 :=
  ⟨by decide, trivial, ⟨by simp [WellScoped], by simp [WellScoped]⟩,
    callVar_wellScoped (by decide) getListProg_wellScoped,
    callVar_wellScoped (by decide) sizeProg_wellScoped, ⟨trivial, by simp [WellScoped]⟩⟩
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Polynomial
open Prog
theorem costConst_wellScoped : costConst.WellScoped 1 :=
  ⟨by decide, trivial, callVar_wellScoped (by decide) sizeProg_wellScoped⟩
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Polynomial
open Prog
theorem costCases_wellScoped : ∀ c ∈ costCases, c.WellScoped 1 := by
  intro c hc
  simp only [costCases, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [costVar_wellScoped, trivial, trivial, trivial, trivial, trivial, costConst_wellScoped]
end MIPRE.Cost.Machine

/-! The uploaded declaration, hoisted to the top level as `solution`. -/
open MIPRE
open MIPRE.Cost
open MIPRE.Cost.Machine
open Polynomial
open MIPRE.Cost.Prog
theorem solution (k : ℕ) (body env kont r : Data) {t : ℕ}
    (hk : k < costCases.length)
    (h : Eval [Data.cons body env] (costCases.getD k .nil) r t) :
    ∃ s ≤ t + 2 * body.size + 2 * env.size + kont.size + k + 14,
      Eval [Data.cons (.cons .nil (.cons (.ofNat k) body)) (.cons env kont)] stepCostProg r s := by
  obtain ⟨s₁, hs₁, hpl⟩ := projLeft_runs
    (E := [Data.ofNat k, body, .nil, .cons (.ofNat k) body, .cons .nil (.cons (.ofNat k) body),
      .cons env kont, .cons (.cons .nil (.cons (.ofNat k) body)) (.cons env kont)])
    (i := 5) (d := .cons env kont) (by simp)
  obtain ⟨s₂, hs₂, hd⟩ := dispatch_runs costCases k 1 0
    (Data.cons body env :: [Data.ofNat k, body, .nil, .cons (.ofNat k) body,
      .cons .nil (.cons (.ofNat k) body), .cons env kont,
      .cons (.cons .nil (.cons (.ofNat k) body)) (.cons env kont)])
    (Data.cons body env) r t hk costCases_wellScoped (by simp) (by simp) h
  have run : Eval [Data.cons (.cons .nil (.cons (.ofNat k) body)) (.cons env kont)] stepCostProg
      r _ :=
    Eval.elim_cons (i := 0) (a := .cons .nil (.cons (.ofNat k) body)) (b := .cons env kont)
      (by simp)
      (Eval.elim_cons (i := 0) (a := .nil) (b := .cons (.ofNat k) body) (by simp)
        (Eval.elim_nil (i := 0) (by simp)
          (Eval.elim_cons (i := 1) (a := .ofNat k) (b := body) (by simp)
            (Eval.let_ (Eval.cons (Eval.var_of_get (i := 1) (v := body) (by simp)) hpl) hd))))
  refine ⟨_, ?_, run⟩
  simp only [Data.size_cons] at hs₁ hs₂
  omega
