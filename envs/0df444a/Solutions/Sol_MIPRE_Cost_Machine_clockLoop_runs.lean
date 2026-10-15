-- Prove2me | solution 1 for MIPRE.Cost.Machine.clockLoop_runs
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-12T16:57:40.622187+00:00
-- url     : https://prove2.me/submissions/2f336070-4540-4c83-a511-d2d980d0e0d3

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/Universal.lean (solution of MIPRE.Cost.Machine.clockLoop_runs);
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
import Theorems.Thm_MIPRE_Cost_Machine_clockBody_prefix
import Theorems.Thm_MIPRE_Cost_Machine_stepCost_le_size
import Theorems.Thm_MIPRE_Cost_Machine_stepProg_runs
import Theorems.Thm_MIPRE_Cost_Machine_subProg_runs

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context; each is used only by proofs. -/
namespace MIPRE.Cost.Machine
theorem costSum_add (c : Cfg) (m n : ℕ) :
    costSum c (m + n) = costSum c m + costSum (step^[m] c) n := by
  induction m generalizing c with
  | zero => simp [costSum]
  | succ m ih =>
    rw [show m + 1 + n = (m + n) + 1 by omega, costSum, ih (step c), costSum,
      Function.iterate_succ_apply]
    omega
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
theorem stepProg_wellScoped : stepProg.WellScoped 1 :=
  ⟨by decide, trivial, by decide, trivial, ⟨by simp [WellScoped], by simp [WellScoped]⟩,
    by decide, callVar_wellScoped (by decide) stepEvProg_wellScoped,
    callVar_wellScoped (by decide) stepRetProg_wellScoped⟩
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
theorem costSum_succ (c : Cfg) (n : ℕ) :
    costSum c (n + 1) = costSum c n + stepCost (step^[n] c) := by
  rw [costSum_add, costSum, costSum]; omega
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Polynomial
open Prog
theorem isFinalProg_wellScoped : isFinalProg.WellScoped 1 := by simp [isFinalProg, WellScoped]
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Polynomial
open Prog
theorem isFinalProg_final (r : Data) (e : Env) :
    ∃ t ≤ r.size + 8, isFinalProg.Runs (Cfg.toData ⟨.ret r, e, []⟩) (.cons .nil r) t := by
  have run : Eval [Cfg.toData ⟨.ret r, e, []⟩] isFinalProg (.cons .nil r) _ :=
    Eval.elim_cons (i := 0) (a := retD r) (b := .cons (.list e) .nil)
      (by simp [Cfg.toData, Ctrl.toData])
      (Eval.elim_cons (i := 0) (a := .cons .nil .nil) (b := r) (by simp [retD])
        (Eval.elim_cons (i := 0) (a := .nil) (b := .nil) (by simp)
          (Eval.elim_cons (i := 5) (a := .list e) (b := .nil) (by simp)
            (Eval.elim_nil (i := 1) (by simp)
              (Eval.cons (Eval.nil _) (Eval.var_of_get (i := 5) (v := r) (by simp)))))))
  exact ⟨_, by omega, run⟩
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
theorem stepBound_mono {S T : ℕ} (h : S ≤ T) : stepBound S ≤ stepBound T :=
  Nat.add_le_add_right (Nat.mul_le_mul (by omega) (by omega)) _
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
theorem subBound_mono {a b a' b' : ℕ} (ha : a ≤ a') (hb : b ≤ b') : subBound a b ≤ subBound a' b' :=
  Nat.mul_le_mul (by omega) (by omega)
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Polynomial
open Prog
theorem stepCostBound_mono {S T : ℕ} (h : S ≤ T) : stepCostBound S ≤ stepCostBound T := by
  unfold stepCostBound
  have := Nat.mul_le_mul (Nat.add_le_add_right h 1) (show 7 * S + 32 ≤ 7 * T + 32 by omega)
  omega
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Polynomial
open Prog
theorem sizeBound_mono {s t : ℕ} (h : s ≤ t) : sizeBound s ≤ sizeBound t := by
  unfold sizeBound
  have := Nat.mul_le_mul (Nat.add_le_add_right h 1) (show 5 * s + 20 ≤ 5 * t + 20 by omega)
  omega
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Polynomial
open Prog
theorem clockBody_final (r : Data) (e : Env) (rem budget theta : Data) (env : Env) :
    ∃ t ≤ 3 * (Cfg.toData ⟨.ret r, e, []⟩).size + 30,
      Eval (clockState (Cfg.toData ⟨.ret r, e, []⟩) rem budget theta :: env) clockBody
        (.cons .nil (.cons (.cons .nil .nil) r)) t := by
  obtain ⟨t₁, ht₁, h₁⟩ := isFinalProg_final r e
  have run : Eval (clockState (Cfg.toData ⟨.ret r, e, []⟩) rem budget theta :: env) clockBody
      (.cons .nil (.cons (.cons .nil .nil) r)) _ :=
    Eval.elim_cons (i := 0) (a := Cfg.toData ⟨.ret r, e, []⟩) (b := .cons rem (.cons budget theta))
      (by simp [clockState])
      (Eval.elim_cons (i := 1) (a := rem) (b := .cons budget theta) (by simp)
        (Eval.elim_cons (i := 1) (a := budget) (b := theta) (by simp)
          (Eval.let_ (callVar_eval (i := 4) isFinalProg_wellScoped
              (v := Cfg.toData ⟨.ret r, e, []⟩) (by simp) h₁)
            (Eval.elim_cons (i := 0) (a := .nil) (b := r) (by simp)
              (Eval.cons (Eval.nil _) (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _))
                (Eval.var_of_get (i := 1) (v := r) (by simp))))))))
  refine ⟨_, ?_, run⟩
  have : r.size ≤ (Cfg.toData ⟨.ret r, e, []⟩).size := by
    simp only [Cfg.toData, Ctrl.toData, retD, Data.size_cons]; omega
  omega
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Polynomial
open Prog
theorem clockBody_budget0 (c : Cfg) (hc : ¬ IsFinal c) (rem theta : Data) (env : Env) :
    ∃ t ≤ (Cfg.toData c).size + 20,
      Eval (clockState c.toData rem (.ofNat 0) theta :: env) clockBody (.cons .nil .nil) t := by
  obtain ⟨t₁, ht₁, h₁⟩ := isFinalProg_nonfinal c hc
  have run : Eval (clockState c.toData rem (.ofNat 0) theta :: env) clockBody
      (.cons .nil .nil) _ :=
    Eval.elim_cons (i := 0) (a := c.toData) (b := .cons rem (.cons (.ofNat 0) theta))
      (by simp [clockState])
      (Eval.elim_cons (i := 1) (a := rem) (b := .cons (.ofNat 0) theta) (by simp)
        (Eval.elim_cons (i := 1) (a := .ofNat 0) (b := theta) (by simp)
          (Eval.let_ (callVar_eval (i := 4) isFinalProg_wellScoped (v := c.toData) (by simp) h₁)
            (Eval.elim_nil (i := 0) (by simp)
              (Eval.elim_nil (i := 1) (by simp [Data.ofNat])
                (Eval.cons (Eval.nil _) (Eval.nil _)))))))
  exact ⟨_, by omega, run⟩
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Polynomial
open Prog
theorem clockRest_stop (c : Cfg) (rem b Θ : ℕ) (env : Env) (hle : stepCost c ≤ rem)
    (hΘ : Θ < ((step c).toData).size) :
    ∃ t ≤ clockRestBound (Cfg.toData c).size Θ rem b,
      Eval (clockEnv c rem b Θ env) (.elim 0 (.cons .nil .nil) clockRest) (.cons .nil .nil) t := by
  obtain ⟨ts, hts, hstep⟩ := stepProg_runs c
  obtain ⟨tz, htz, hsz⟩ := sizeProg_runs (step c).toData
  obtain ⟨tu, htu, hsub⟩ := subProg_runs ((step c).toData).size Θ []
  have hsize : ((step c).toData).size ≤ ts := hstep.size_le
  have run : Eval (clockEnv c rem b Θ env) (.elim 0 (.cons .nil .nil) clockRest)
      (.cons .nil .nil) _ :=
    Eval.elim_cons (i := 0) (a := .cons .nil .nil) (b := .ofNat (rem - stepCost c))
      (by simp [clockEnv, subResult, hle])
      (Eval.let_ (callVar_eval (i := 11) stepProg_wellScoped (v := c.toData) (by simp [clockEnv])
          hstep)
        (Eval.let_ (Eval.let_ (callVar_eval (i := 0) sizeProg_wellScoped (v := (step c).toData)
              (by simp) hsz)
            (Eval.cons (Eval.var_of_get (i := 0) (v := .ofNat ((step c).toData).size) (by simp))
              (Eval.var_of_get (i := 10) (v := .ofNat Θ) (by simp [clockEnv]))))
          (Eval.let_ (callVar_eval (i := 0) subProg_wellScoped
              (v := .cons (.ofNat ((step c).toData).size) (.ofNat Θ)) (by simp) hsub)
            (Eval.elim_nil (i := 0) (by simp [subResult, Nat.not_le.2 hΘ])
              (Eval.cons (Eval.nil _) (Eval.nil _))))))
  refine ⟨_, ?_, run⟩
  have h1 : tz ≤ sizeBound ((step c).toData).size := htz
  have h2 := sizeBound_mono (hsize.trans hts)
  have h3 := subBound_mono (hsize.trans hts) (le_refl Θ)
  unfold clockRestBound
  try simp only [Data.size_cons, Data.size_ofNat] at *
  omega
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Polynomial
open Prog
theorem clockRest_continue (c : Cfg) (rem b Θ : ℕ) (env : Env) (hle : stepCost c ≤ rem)
    (hΘ : ((step c).toData).size ≤ Θ) :
    ∃ t ≤ clockRestBound (Cfg.toData c).size Θ rem b,
      Eval (clockEnv c rem b Θ env) (.elim 0 (.cons .nil .nil) clockRest)
        (.cons (.cons .nil .nil)
          (clockState (step c).toData (.ofNat (rem - stepCost c)) (.ofNat b) (.ofNat Θ))) t := by
  obtain ⟨ts, hts, hstep⟩ := stepProg_runs c
  obtain ⟨tz, htz, hsz⟩ := sizeProg_runs (step c).toData
  obtain ⟨tu, htu, hsub⟩ := subProg_runs ((step c).toData).size Θ []
  have hsize : ((step c).toData).size ≤ ts := hstep.size_le
  have run : Eval (clockEnv c rem b Θ env) (.elim 0 (.cons .nil .nil) clockRest)
      (.cons (.cons .nil .nil)
        (clockState (step c).toData (.ofNat (rem - stepCost c)) (.ofNat b) (.ofNat Θ))) _ :=
    Eval.elim_cons (i := 0) (a := .cons .nil .nil) (b := .ofNat (rem - stepCost c))
      (by simp [clockEnv, subResult, hle])
      (Eval.let_ (callVar_eval (i := 11) stepProg_wellScoped (v := c.toData) (by simp [clockEnv])
          hstep)
        (Eval.let_ (Eval.let_ (callVar_eval (i := 0) sizeProg_wellScoped (v := (step c).toData)
              (by simp) hsz)
            (Eval.cons (Eval.var_of_get (i := 0) (v := .ofNat ((step c).toData).size) (by simp))
              (Eval.var_of_get (i := 10) (v := .ofNat Θ) (by simp [clockEnv]))))
          (Eval.let_ (callVar_eval (i := 0) subProg_wellScoped
              (v := .cons (.ofNat ((step c).toData).size) (.ofNat Θ)) (by simp) hsub)
            (Eval.elim_cons (i := 0) (a := .cons .nil .nil)
              (b := .ofNat (Θ - ((step c).toData).size)) (by simp [subResult, hΘ])
              (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _))
                (Eval.cons (Eval.var_of_get (i := 4) (v := (step c).toData) (by simp))
                  (Eval.cons (Eval.var_of_get (i := 6) (v := .ofNat (rem - stepCost c)) (by simp))
                    (Eval.cons (Eval.var_of_get (i := 10) (v := .ofNat b) (by simp [clockEnv]))
                      (Eval.var_of_get (i := 13) (v := .ofNat Θ) (by simp [clockEnv]))))))))))
  refine ⟨_, ?_, run⟩
  have h1 : tz ≤ sizeBound ((step c).toData).size := htz
  have h2 := sizeBound_mono (hsize.trans hts)
  have h3 := subBound_mono (hsize.trans hts) (le_refl Θ)
  unfold clockRestBound
  try simp only [Data.size_cons, Data.size_ofNat] at *
  omega
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Polynomial
open Prog
/-- The cost of one non-final iteration is at most `clockBodyBound Θ k`. -/
theorem clockBody_cost_le {S Θ k rem b cost t₂ t₁ : ℕ} (hS : S ≤ Θ) (hrem : rem ≤ k)
    (hb : b ≤ 3 * k) (hcost : cost ≤ S) (ht₂ : t₂ ≤ clockRestBound S Θ rem b)
    (ht₁ : t₁ ≤ t₂ + stepCostBound S + subBound cost rem + 4 * S + 4 * rem + 30) :
    t₁ ≤ clockBodyBound Θ k := by
  have h1 : stepCostBound S ≤ stepCostBound Θ := stepCostBound_mono hS
  have h2 : subBound cost rem ≤ subBound Θ k := subBound_mono (hcost.trans hS) hrem
  have h3 : stepBound S ≤ stepBound Θ := stepBound_mono hS
  have h4 : sizeBound (stepBound S) ≤ sizeBound (stepBound Θ) := sizeBound_mono h3
  have h5 : subBound (stepBound S) Θ ≤ subBound (stepBound Θ) Θ := subBound_mono h3 le_rfl
  unfold clockRestBound at ht₂
  unfold clockBodyBound
  omega
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Polynomial
open Prog
theorem clockBodyBound_ge (Θ k : ℕ) : 12 * Θ + 200 ≤ clockBodyBound Θ k := by
  unfold clockBodyBound; omega
end MIPRE.Cost.Machine

/-! The uploaded declaration, hoisted to the top level as `solution`. -/
open MIPRE
open MIPRE.Cost
open MIPRE.Cost.Machine
open Polynomial
open MIPRE.Cost.Prog
theorem solution (c₀ : Cfg) (k Θ : ℕ) (env : Env) : ∀ (b n : ℕ), b ≤ 3 * k + 1 →
    costSum c₀ n ≤ k → (step^[n] c₀).toData.size ≤ Θ →
    ∃ t ≤ (b + 1) * (clockBodyBound Θ k + 1),
      Eval (clockState (step^[n] c₀).toData (.ofNat (k - costSum c₀ n)) (.ofNat b) (.ofNat Θ)
          :: env) (.loop clockBody) (clockRun c₀ k Θ b n) t := by
  intro b
  induction b with
  | zero =>
    intro n hb hcost hΘ
    have hB := clockBodyBound_ge Θ k
    have hmul := Nat.le_mul_of_pos_left (clockBodyBound Θ k + 1) (show 0 < 0 + 1 by omega)
    by_cases hf : IsFinal (step^[n] c₀)
    · obtain ⟨r, e, hr⟩ := id hf
      simp only [clockRun, if_pos hf]
      rw [hr] at hΘ ⊢
      obtain ⟨t, ht, hbody⟩ :=
        clockBody_final r e (.ofNat (k - costSum c₀ n)) (.ofNat 0) (.ofNat Θ) env
      exact ⟨t + 1, by omega, Eval.loop_stop hbody⟩
    · simp only [clockRun, if_neg hf]
      obtain ⟨t, ht, hbody⟩ := clockBody_budget0 (step^[n] c₀) hf (.ofNat (k - costSum c₀ n))
        (.ofNat Θ) env
      exact ⟨t + 1, by omega, Eval.loop_stop hbody⟩
  | succ b ih =>
    intro n hb hcost hΘ
    have hB := clockBodyBound_ge Θ k
    have hmul := Nat.le_mul_of_pos_left (clockBodyBound Θ k + 1) (show 0 < b + 1 + 1 by omega)
    by_cases hf : IsFinal (step^[n] c₀)
    · obtain ⟨r, e, hr⟩ := id hf
      simp only [clockRun, if_pos hf]
      rw [hr] at hΘ ⊢
      obtain ⟨t, ht, hbody⟩ :=
        clockBody_final r e (.ofNat (k - costSum c₀ n)) (.ofNat (b + 1)) (.ofNat Θ) env
      exact ⟨t + 1, by omega, Eval.loop_stop hbody⟩
    · simp only [clockRun, if_neg hf]
      have hcost' := stepCost_le_size (step^[n] c₀)
      by_cases hc : costSum c₀ (n + 1) ≤ k
      · have hle : stepCost (step^[n] c₀) ≤ k - costSum c₀ n := by
          rw [costSum_succ] at hc; omega
        have hrem : k - costSum c₀ n - stepCost (step^[n] c₀) = k - costSum c₀ (n + 1) := by
          rw [costSum_succ]; omega
        by_cases hΘ' : (step^[n + 1] c₀).toData.size ≤ Θ
        · rw [if_pos ⟨hc, hΘ'⟩]
          obtain ⟨t₂, ht₂, hrest⟩ := clockRest_continue (step^[n] c₀) (k - costSum c₀ n) b Θ env
            hle (by rwa [Function.iterate_succ_apply'] at hΘ')
          obtain ⟨t₁, ht₁, hbody⟩ := clockBody_prefix (step^[n] c₀) hf (k - costSum c₀ n) b Θ
            env _ hrest
          obtain ⟨t₃, ht₃, hloop⟩ := ih (n + 1) (by omega) hc hΘ'
          rw [Function.iterate_succ_apply', ← hrem] at hloop
          refine ⟨t₁ + t₃ + 1, ?_, Eval.loop_step hbody hloop⟩
          have : t₁ ≤ clockBodyBound Θ k := clockBody_cost_le hΘ (by omega) (by omega) hcost' ht₂ ht₁
          rw [Nat.succ_mul]
          omega
        · rw [if_neg (fun h => hΘ' h.2)]
          obtain ⟨t₂, ht₂, hrest⟩ := clockRest_stop (step^[n] c₀) (k - costSum c₀ n) b Θ env
            hle (by rw [Function.iterate_succ_apply'] at hΘ'; omega)
          obtain ⟨t₁, ht₁, hbody⟩ := clockBody_prefix (step^[n] c₀) hf (k - costSum c₀ n) b Θ
            env _ hrest
          refine ⟨t₁ + 1, ?_, Eval.loop_stop hbody⟩
          have : t₁ ≤ clockBodyBound Θ k := clockBody_cost_le hΘ (by omega) (by omega) hcost' ht₂ ht₁
          omega
      · rw [if_neg (fun h => hc h.1)]
        have hlt : k - costSum c₀ n < stepCost (step^[n] c₀) := by
          rw [costSum_succ] at hc; omega
        have hrest : Eval (clockEnv (step^[n] c₀) (k - costSum c₀ n) b Θ env)
            (.elim 0 (.cons .nil .nil) clockRest) (.cons .nil .nil) _ :=
          Eval.elim_nil (i := 0) (by simp [clockEnv, subResult, Nat.not_le.2 hlt])
            (Eval.cons (Eval.nil _) (Eval.nil _))
        obtain ⟨t₁, ht₁, hbody⟩ := clockBody_prefix (step^[n] c₀) hf (k - costSum c₀ n) b Θ
          env _ hrest
        refine ⟨t₁ + 1, ?_, Eval.loop_stop hbody⟩
        have : t₁ ≤ clockBodyBound Θ k := clockBody_cost_le hΘ (by omega) (by omega) hcost'
          (show 4 ≤ clockRestBound (Cfg.toData (step^[n] c₀)).size Θ (k - costSum c₀ n) b by
            unfold clockRestBound; omega) ht₁
        omega
