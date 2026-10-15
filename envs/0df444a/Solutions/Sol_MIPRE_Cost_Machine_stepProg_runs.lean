-- Prove2me | solution 1 for MIPRE.Cost.Machine.stepProg_runs
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-12T16:44:32.377244+00:00
-- url     : https://prove2.me/submissions/b0cde860-5648-4a2c-a66c-059ca16f5e2d

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/Interpreter.lean (solution of MIPRE.Cost.Machine.stepProg_runs);
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
import Theorems.Thm_MIPRE_Cost_Machine_stepData_toData
import Theorems.Thm_MIPRE_Cost_Machine_stepEvProg_runs
import Theorems.Thm_MIPRE_Cost_Machine_stepRetProg_runs_cons

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context; each is used only by proofs. -/
namespace MIPRE.Cost.Prog
theorem esize_eq_size_toData (p : Prog) : esize p = p.toData.size := rfl
end MIPRE.Cost.Prog

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
theorem evVar_wellScoped : evVar.WellScoped 1 :=
  ⟨by decide, trivial, by decide, trivial, ⟨by simp [WellScoped], by simp [WellScoped]⟩,
    callVar_wellScoped (by decide) getListProg_wellScoped, ⟨⟨trivial, trivial⟩, by simp [WellScoped]⟩,
    by simp [WellScoped]⟩
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Prog
theorem evNil_wellScoped : evNil.WellScoped 1 := by simp [evNil, WellScoped]
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Prog
theorem evCons_wellScoped : evCons.WellScoped 1 := by simp [evCons, WellScoped]
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Prog
theorem evLet_wellScoped : evLet.WellScoped 1 := by simp [evLet, WellScoped]
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Prog
theorem evLoop_wellScoped : evLoop.WellScoped 1 := by simp [evLoop, WellScoped]
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Prog
theorem evConst_wellScoped : evConst.WellScoped 1 := by simp [evConst, WellScoped]
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Prog
theorem evElim_wellScoped : evElim.WellScoped 1 :=
  ⟨by decide, trivial, by decide, trivial, by decide, trivial, by decide, trivial,
    ⟨by simp [WellScoped], by simp [WellScoped]⟩,
    callVar_wellScoped (by decide) getListProg_wellScoped, by simp [WellScoped]⟩
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
open Prog
theorem evCases_wellScoped : ∀ c ∈ evCases, c.WellScoped 1 := by
  intro c hc
  simp only [evCases, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [evVar_wellScoped, evNil_wellScoped, evCons_wellScoped, evElim_wellScoped,
    evLet_wellScoped, evLoop_wellScoped, evConst_wellScoped]
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Prog
theorem stepEvProg_wellScoped : stepEvProg.WellScoped 1 :=
  ⟨by decide, trivial, by decide, trivial, by decide, trivial,
    ⟨by simp [WellScoped], by simp [WellScoped], by simp [WellScoped]⟩,
    ⟨by simp [WellScoped], dispatch_wellScoped evCases 0 1 9 (by omega) (by omega) evCases_wellScoped⟩⟩
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Prog
theorem retCons1_wellScoped : retCons1.WellScoped 1 := by simp [retCons1, WellScoped]
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Prog
theorem retCons2_wellScoped : retCons2.WellScoped 1 := by simp [retCons2, WellScoped]
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Prog
theorem retLet1_wellScoped : retLet1.WellScoped 1 := by simp [retLet1, WellScoped]
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Prog
theorem retLoop1_wellScoped : retLoop1.WellScoped 1 := by
  simp [retLoop1, projRight, WellScoped]
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Prog
theorem retCases_wellScoped : ∀ c ∈ retCases, c.WellScoped 1 := by
  intro c hc
  simp only [retCases, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  exacts [retCons1_wellScoped, retCons2_wellScoped, retLet1_wellScoped, retLoop1_wellScoped]
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Prog
theorem stepRetProg_wellScoped : stepRetProg.WellScoped 1 :=
  ⟨by decide, trivial, by decide, trivial, by decide,
    ⟨⟨⟨trivial, trivial⟩, by simp [WellScoped]⟩, by simp [WellScoped]⟩,
    by decide, trivial,
    ⟨by simp [WellScoped], by simp [WellScoped], by simp [WellScoped], by simp [WellScoped]⟩,
    ⟨by simp [WellScoped], dispatch_wellScoped retCases 0 1 11 (by omega) (by omega) retCases_wellScoped⟩⟩
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Prog
theorem stepRetProg_runs_nil (v env : Data) :
    ∃ s ≤ v.size + env.size + 12,
      stepRetProg.Runs (.cons v (.cons env .nil)) (stepRet v env .nil) s := by
  have run : Eval [Data.cons v (.cons env .nil)] stepRetProg (.cons (retD v) (.cons env .nil)) _ :=
    Eval.elim_cons (i := 0) (a := v) (b := .cons env .nil) (by simp)
      (Eval.elim_cons (i := 1) (a := env) (b := .nil) (by simp)
        (Eval.elim_nil (i := 1) (by simp)
          (Eval.cons (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _))
              (Eval.var_of_get (i := 2) (v := v) (by simp)))
            (Eval.var_of_get (i := 3) (v := .cons env .nil) (by simp)))))
  refine ⟨_, ?_, by simpa [Prog.Runs, stepRet] using run⟩
  ((try simp only [MIPRE.Cost.Data.size_cons, MIPRE.Cost.Data.size_nil, MIPRE.Cost.Data.size_ofNat, MIPRE.Cost.Machine.Frame.toData, MIPRE.Cost.Machine.Cfg.toData, MIPRE.Cost.Machine.Ctrl.toData, MIPRE.Cost.Machine.evD, MIPRE.Cost.Machine.retD, MIPRE.Cost.Prog.toData, MIPRE.Cost.Data.list_cons, MIPRE.Cost.Data.list_nil, List.map_cons, List.map_nil] at *); all_goals omega)
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Prog
theorem le_stepBound_of_le {c S T : ℕ} (hc : c ≤ 41 * S + 240) (hS : S ≤ T) :
    c ≤ stepBound T := by
  unfold stepBound; nlinarith [Nat.mul_le_mul hS hS]
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Prog
theorem le_stepBound_of_quad {c S T : ℕ} (hc : c ≤ (S + 1) * (S + 30) + 100 + 3 * S + 60)
    (hS : S + 4 ≤ T) : c ≤ stepBound T := by
  unfold stepBound; nlinarith [Nat.mul_le_mul hS hS]
end MIPRE.Cost.Machine

/-! The uploaded declaration, hoisted to the top level as `solution`. -/
open MIPRE
open MIPRE.Cost
open MIPRE.Cost.Machine
open MIPRE.Cost.Prog
theorem solution (c : Cfg) :
    ∃ s ≤ stepBound (Cfg.toData c).size, stepProg.Runs c.toData (step c).toData s := by
  rw [← stepData_toData]
  obtain ⟨ctrl, env, kont⟩ := c
  cases ctrl with
  | ev p =>
    obtain ⟨s, hs, hev⟩ := stepEvProg_runs p (Data.list env) (Data.list (kont.map Frame.toData))
    have run : Eval [Cfg.toData ⟨.ev p, env, kont⟩] stepProg
        (stepEv p.toData (Data.list env) (Data.list (kont.map Frame.toData))) _ :=
      Eval.elim_cons (i := 0) (a := evD p.toData)
        (b := .cons (.list env) (.list (kont.map Frame.toData))) (by simp [Cfg.toData, Ctrl.toData])
        (Eval.elim_cons (i := 0) (a := .nil) (b := p.toData) (by simp [evD])
          (Eval.let_ (Eval.cons (Eval.var_of_get (i := 1) (v := p.toData) (by simp))
              (Eval.var_of_get (i := 3) (v := .cons (.list env) (.list (kont.map Frame.toData)))
                (by simp)))
            (Eval.elim_nil (i := 1) (by simp)
              (callVar_eval (i := 0) stepEvProg_wellScoped
                (v := .cons p.toData (.cons (.list env) (.list (kont.map Frame.toData))))
                (by simp) hev))))
    refine ⟨_, ?_, by simpa [Prog.Runs, stepData, Cfg.toData, Ctrl.toData, evD] using run⟩
    refine le_stepBound_of_quad
      (S := esize p + (Data.list env).size + (Data.list (kont.map Frame.toData)).size) ?_ ?_
    · unfold stepEvBound at hs
      rw [Prog.esize_eq_size_toData] at hs ⊢
      ((try simp only [MIPRE.Cost.Data.size_cons, MIPRE.Cost.Data.size_nil, MIPRE.Cost.Data.size_ofNat, MIPRE.Cost.Machine.Frame.toData, MIPRE.Cost.Machine.Cfg.toData, MIPRE.Cost.Machine.Ctrl.toData, MIPRE.Cost.Machine.evD, MIPRE.Cost.Machine.retD, MIPRE.Cost.Prog.toData, MIPRE.Cost.Data.list_cons, MIPRE.Cost.Data.list_nil, List.map_cons, List.map_nil] at *); all_goals omega)
    · rw [Prog.esize_eq_size_toData]
      ((try simp only [MIPRE.Cost.Data.size_cons, MIPRE.Cost.Data.size_nil, MIPRE.Cost.Data.size_ofNat, MIPRE.Cost.Machine.Frame.toData, MIPRE.Cost.Machine.Cfg.toData, MIPRE.Cost.Machine.Ctrl.toData, MIPRE.Cost.Machine.evD, MIPRE.Cost.Machine.retD, MIPRE.Cost.Prog.toData, MIPRE.Cost.Data.list_cons, MIPRE.Cost.Data.list_nil, List.map_cons, List.map_nil] at *); all_goals omega)
  | ret v =>
    cases kont with
    | nil =>
      obtain ⟨s, hs, hret⟩ := stepRetProg_runs_nil v (Data.list env)
      have run : Eval [Cfg.toData ⟨.ret v, env, []⟩] stepProg (stepRet v (Data.list env) .nil) _ :=
        Eval.elim_cons (i := 0) (a := retD v) (b := .cons (.list env) .nil)
          (by simp [Cfg.toData, Ctrl.toData])
          (Eval.elim_cons (i := 0) (a := .cons .nil .nil) (b := v) (by simp [retD])
            (Eval.let_ (Eval.cons (Eval.var_of_get (i := 1) (v := v) (by simp))
                (Eval.var_of_get (i := 3) (v := .cons (.list env) .nil) (by simp)))
              (Eval.elim_cons (i := 1) (a := .nil) (b := .nil) (by simp)
                (callVar_eval (i := 2) stepRetProg_wellScoped (v := .cons v (.cons (.list env) .nil))
                  (by simp) hret))))
      refine ⟨_, ?_, by simpa [Prog.Runs, stepData, Cfg.toData, Ctrl.toData, retD] using run⟩
      refine le_stepBound_of_le (S := v.size + (Data.list env).size) ?_ ?_
      · ((try simp only [MIPRE.Cost.Data.size_cons, MIPRE.Cost.Data.size_nil, MIPRE.Cost.Data.size_ofNat, MIPRE.Cost.Machine.Frame.toData, MIPRE.Cost.Machine.Cfg.toData, MIPRE.Cost.Machine.Ctrl.toData, MIPRE.Cost.Machine.evD, MIPRE.Cost.Machine.retD, MIPRE.Cost.Prog.toData, MIPRE.Cost.Data.list_cons, MIPRE.Cost.Data.list_nil, List.map_cons, List.map_nil] at *); all_goals omega)
      · ((try simp only [MIPRE.Cost.Data.size_cons, MIPRE.Cost.Data.size_nil, MIPRE.Cost.Data.size_ofNat, MIPRE.Cost.Machine.Frame.toData, MIPRE.Cost.Machine.Cfg.toData, MIPRE.Cost.Machine.Ctrl.toData, MIPRE.Cost.Machine.evD, MIPRE.Cost.Machine.retD, MIPRE.Cost.Prog.toData, MIPRE.Cost.Data.list_cons, MIPRE.Cost.Data.list_nil, List.map_cons, List.map_nil] at *); all_goals omega)
    | cons f k =>
      obtain ⟨s, hs, hret⟩ :=
        stepRetProg_runs_cons v (Data.list env) f (Data.list (k.map Frame.toData))
      have run : Eval [Cfg.toData ⟨.ret v, env, f :: k⟩] stepProg
          (stepRet v (Data.list env) (.cons (Frame.toData f) (Data.list (k.map Frame.toData)))) _ :=
        Eval.elim_cons (i := 0) (a := retD v)
          (b := .cons (.list env) (.cons (Frame.toData f) (Data.list (k.map Frame.toData))))
          (by simp [Cfg.toData, Ctrl.toData])
          (Eval.elim_cons (i := 0) (a := .cons .nil .nil) (b := v) (by simp [retD])
            (Eval.let_ (Eval.cons (Eval.var_of_get (i := 1) (v := v) (by simp))
                (Eval.var_of_get (i := 3)
                  (v := .cons (.list env) (.cons (Frame.toData f) (Data.list (k.map Frame.toData))))
                  (by simp)))
              (Eval.elim_cons (i := 1) (a := .nil) (b := .nil) (by simp)
                (callVar_eval (i := 2) stepRetProg_wellScoped
                  (v := .cons v (.cons (.list env)
                    (.cons (Frame.toData f) (Data.list (k.map Frame.toData)))))
                  (by simp) hret))))
      refine ⟨_, ?_, by simpa [Prog.Runs, stepData, Cfg.toData, Ctrl.toData, retD] using run⟩
      refine le_stepBound_of_le
        (S := v.size + (Data.list env).size + (Frame.toData f).size +
          (Data.list (k.map Frame.toData)).size) ?_ ?_
      · unfold stepRetBound at hs
        ((try simp only [MIPRE.Cost.Data.size_cons, MIPRE.Cost.Data.size_nil, MIPRE.Cost.Data.size_ofNat, MIPRE.Cost.Machine.Frame.toData, MIPRE.Cost.Machine.Cfg.toData, MIPRE.Cost.Machine.Ctrl.toData, MIPRE.Cost.Machine.evD, MIPRE.Cost.Machine.retD, MIPRE.Cost.Prog.toData, MIPRE.Cost.Data.list_cons, MIPRE.Cost.Data.list_nil, List.map_cons, List.map_nil] at *); all_goals omega)
      · ((try simp only [MIPRE.Cost.Data.size_cons, MIPRE.Cost.Data.size_nil, MIPRE.Cost.Data.size_ofNat, MIPRE.Cost.Machine.Frame.toData, MIPRE.Cost.Machine.Cfg.toData, MIPRE.Cost.Machine.Ctrl.toData, MIPRE.Cost.Machine.evD, MIPRE.Cost.Machine.retD, MIPRE.Cost.Prog.toData, MIPRE.Cost.Data.list_cons, MIPRE.Cost.Data.list_nil, List.map_cons, List.map_nil] at *); all_goals omega)
