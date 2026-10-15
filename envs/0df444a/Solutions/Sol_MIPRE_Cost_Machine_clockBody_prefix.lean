-- Prove2me | solution 1 for MIPRE.Cost.Machine.clockBody_prefix
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-12T16:56:51.815914+00:00
-- url     : https://prove2.me/submissions/32441f33-5021-4b91-9ad0-643860baf3ae

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/Universal.lean (solution of MIPRE.Cost.Machine.clockBody_prefix);
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
import Theorems.Thm_MIPRE_Cost_Machine_stepCostProg_runs
import Theorems.Thm_MIPRE_Cost_Machine_stepCost_le_size
import Theorems.Thm_MIPRE_Cost_Machine_subProg_runs

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context; each is used only by proofs. -/
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
open Prog
theorem dispatch_wellScoped : ∀ (cs : List Prog) (i idx n : ℕ), i < n → idx < n →
    (∀ c ∈ cs, c.WellScoped 1) → (dispatch cs i idx).WellScoped n
  | [], _, _, _, _, _, _ => trivial
  | [c], _, idx, n, _, hidx, hcs => callVar_wellScoped hidx (hcs c (by simp))
  | c :: c' :: cs, i, idx, n, hi, hidx, hcs =>
    ⟨hi, callVar_wellScoped hidx (hcs c (by simp)),
      dispatch_wellScoped (c' :: cs) 1 (idx + 2) (n + 2) (by omega) (by omega)
        (fun d hd => hcs d (List.mem_cons_of_mem c hd))⟩
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Polynomial
open Prog
theorem isFinalProg_wellScoped : isFinalProg.WellScoped 1 := by simp [isFinalProg, WellScoped]
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Polynomial
open Prog
theorem isFinalProg_nonfinal (c : Cfg) (h : ¬ IsFinal c) :
    ∃ t ≤ 8, isFinalProg.Runs c.toData .nil t := by
  obtain ⟨ctrl, env, kont⟩ := c
  cases ctrl with
  | ev p =>
    have run : Eval [Cfg.toData ⟨.ev p, env, kont⟩] isFinalProg .nil _ :=
      Eval.elim_cons (i := 0) (a := evD p.toData)
        (b := .cons (.list env) (.list (kont.map Frame.toData))) (by simp [Cfg.toData, Ctrl.toData])
        (Eval.elim_cons (i := 0) (a := .nil) (b := p.toData) (by simp [evD])
          (Eval.elim_nil (i := 0) (by simp) (Eval.nil _)))
    exact ⟨_, by omega, run⟩
  | ret v =>
    cases kont with
    | nil => exact absurd ⟨v, env, rfl⟩ h
    | cons f k =>
      have run : Eval [Cfg.toData ⟨.ret v, env, f :: k⟩] isFinalProg .nil _ :=
        Eval.elim_cons (i := 0) (a := retD v)
          (b := .cons (.list env) (.cons (Frame.toData f) (.list (k.map Frame.toData))))
          (by simp [Cfg.toData, Ctrl.toData])
          (Eval.elim_cons (i := 0) (a := .cons .nil .nil) (b := v) (by simp [retD])
            (Eval.elim_cons (i := 0) (a := .nil) (b := .nil) (by simp)
              (Eval.elim_cons (i := 5) (a := .list env)
                (b := .cons (Frame.toData f) (.list (k.map Frame.toData))) (by simp)
                (Eval.elim_cons (i := 1) (a := Frame.toData f) (b := .list (k.map Frame.toData))
                  (by simp) (Eval.nil _)))))
      exact ⟨_, by omega, run⟩
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Polynomial
open Prog
theorem subBody_wellScoped : subBody.WellScoped 1 := by simp [subBody, WellScoped]
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Polynomial
open Prog
theorem subProg_wellScoped : subProg.WellScoped 1 := ⟨Nat.zero_lt_one, subBody_wellScoped⟩
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

namespace MIPRE.Cost.Machine
open Polynomial
open Prog
theorem stepCostRet_wellScoped : stepCostRet.WellScoped 7 := by simp [stepCostRet, WellScoped]
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Polynomial
open Prog
theorem stepCostEv_wellScoped : stepCostEv.WellScoped 5 :=
  ⟨by decide, trivial, ⟨by simp [WellScoped], by simp [projLeft, WellScoped]⟩,
    dispatch_wellScoped costCases 1 0 8 (by omega) (by omega) costCases_wellScoped⟩
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Polynomial
open Prog
theorem stepCostProg_wellScoped : stepCostProg.WellScoped 1 :=
  ⟨by decide, trivial, by decide, trivial, by decide, stepCostEv_wellScoped, stepCostRet_wellScoped⟩
end MIPRE.Cost.Machine

/-! The uploaded declaration, hoisted to the top level as `solution`. -/
open MIPRE
open MIPRE.Cost
open MIPRE.Cost.Machine
open Polynomial
open MIPRE.Cost.Prog
theorem solution (c : Cfg) (hc : ¬ IsFinal c) (rem b Θ : ℕ) (env : Env) (r : Data)
    {t : ℕ} (hrest : Eval (clockEnv c rem b Θ env) (.elim 0 (.cons .nil .nil) clockRest) r t) :
    ∃ s ≤ t + stepCostBound (Cfg.toData c).size + subBound (stepCost c) rem +
        4 * (Cfg.toData c).size + 4 * rem + 30,
      Eval (clockState c.toData (.ofNat rem) (.ofNat (b + 1)) (.ofNat Θ) :: env) clockBody r s := by
  obtain ⟨t₁, ht₁, h₁⟩ := isFinalProg_nonfinal c hc
  obtain ⟨t₂, ht₂, h₂⟩ := stepCostProg_runs c
  obtain ⟨t₃, ht₃, h₃⟩ := subProg_runs (stepCost c) rem []
  have hcost := stepCost_le_size c
  have run : Eval (clockState c.toData (.ofNat rem) (.ofNat (b + 1)) (.ofNat Θ) :: env) clockBody
      r _ :=
    Eval.elim_cons (i := 0) (a := c.toData)
      (b := .cons (.ofNat rem) (.cons (.ofNat (b + 1)) (.ofNat Θ))) (by simp [clockState])
      (Eval.elim_cons (i := 1) (a := .ofNat rem) (b := .cons (.ofNat (b + 1)) (.ofNat Θ)) (by simp)
        (Eval.elim_cons (i := 1) (a := .ofNat (b + 1)) (b := .ofNat Θ) (by simp)
          (Eval.let_ (callVar_eval (i := 4) isFinalProg_wellScoped (v := c.toData) (by simp) h₁)
            (Eval.elim_nil (i := 0) (by simp)
              (Eval.elim_cons (i := 1) (a := .nil) (b := .ofNat b) (by simp [Data.ofNat])
                (Eval.let_ (Eval.cons (callVar_eval (i := 7) stepCostProg_wellScoped
                      (v := c.toData) (by simp) h₂)
                    (Eval.var_of_get (i := 5) (v := .ofNat rem) (by simp)))
                  (Eval.let_ (callVar_eval (i := 0) subProg_wellScoped
                      (v := .cons (.ofNat (stepCost c)) (.ofNat rem)) (by simp) h₃)
                    hrest)))))))
  refine ⟨_, ?_, run⟩
  try simp only [Data.size_cons, Data.size_ofNat] at *
  omega
