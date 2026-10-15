-- Prove2me | solution 1 for MIPRE.Cost.Machine.stepCostProg_runs
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-12T16:56:01.847926+00:00
-- url     : https://prove2.me/submissions/5fed9da7-1336-4b41-9fa1-0b75f608132d

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/Universal.lean (solution of MIPRE.Cost.Machine.stepCostProg_runs);
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
import Theorems.Thm_MIPRE_Cost_Machine_getListProg_runs
import Theorems.Thm_MIPRE_Cost_Machine_stepCostProg_ev

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context; each is used only by proofs. -/
namespace MIPRE.Cost.Data
theorem getList_list (l : List Data) (i : ℕ) : getList (Data.list l) i = Env.get l i := by
  induction i generalizing l with
  | zero => cases l <;> rfl
  | succ i ih =>
    unfold getList
    rw [Function.iterate_succ_apply]
    cases l with
    | nil => simp [Function.iterate_fixed right_nil, Env.get_nil]
    | cons a l => simpa [getList, Function.iterate_succ_apply] using ih l
end MIPRE.Cost.Data

namespace MIPRE.Cost.Machine
open Prog
theorem size_left_le (d : Data) : d.left.size ≤ d.size := by cases d <;> simp; omega
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Prog
theorem size_right_le (d : Data) : d.right.size ≤ d.size := by cases d <;> simp; omega
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Prog
theorem size_getList_le (env : Data) (n : ℕ) : (Data.getList env n).size ≤ env.size := by
  unfold Data.getList
  refine (size_left_le _).trans ?_
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply']; exact (size_right_le _).trans ih
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
theorem stepCostBound_mono {S T : ℕ} (h : S ≤ T) : stepCostBound S ≤ stepCostBound T := by
  unfold stepCostBound
  have := Nat.mul_le_mul (Nat.add_le_add_right h 1) (show 7 * S + 32 ≤ 7 * T + 32 by omega)
  omega
end MIPRE.Cost.Machine

/-! The uploaded declaration, hoisted to the top level as `solution`. -/
open MIPRE
open MIPRE.Cost
open MIPRE.Cost.Machine
open Polynomial
open MIPRE.Cost.Prog
theorem solution (c : Cfg) :
    ∃ t ≤ stepCostBound (Cfg.toData c).size,
      stepCostProg.Runs c.toData (.ofNat (stepCost c)) t := by
  obtain ⟨ctrl, env, kont⟩ := c
  cases ctrl with
  | ev p =>
    -- the dispatch environment
    cases p with
    | var i =>
      obtain ⟨tg, htg, hg⟩ := getListProg_runs (.ofNat i) (.list env) []
      set w := Data.getList (.list env) (Data.unaryToNat (.ofNat i)) with hw
      obtain ⟨ts, hts, hsz⟩ := sizeProg_runs w
      have hcase : Eval [Data.cons (.ofNat i) (.list env)] (costCases.getD 0 .nil)
          (.ofNat (w.size + 1)) _ :=
        Eval.elim_cons (i := 0) (a := .ofNat i) (b := .list env) (by simp)
          (Eval.let_ (Eval.cons (Eval.var_of_get (i := 1) (v := .list env) (by simp))
              (Eval.var_of_get (i := 0) (v := .ofNat i) (by simp)))
            (Eval.let_ (callVar_eval (i := 0) getListProg_wellScoped
                (v := .cons (.list env) (.ofNat i)) (by simp) hg)
              (Eval.let_ (callVar_eval (i := 0) sizeProg_wellScoped (v := w) (by simp) hsz)
                (Eval.cons (Eval.nil _) (Eval.var_of_get (i := 0) (v := .ofNat w.size) (by simp))))))
      obtain ⟨s, hs, run⟩ := stepCostProg_ev 0 (.ofNat i) (.list env)
        (.list (kont.map Frame.toData)) _ (by simp [costCases]) hcase
      refine ⟨s, ?_, ?_⟩
      · have hw' : w.size ≤ (Data.list env).size := size_getList_le _ _
        obtain ⟨E, hE⟩ : ∃ E, E = (Data.ofNat i).size + (Data.list env).size +
          (Data.list (kont.map Frame.toData)).size + 6 := ⟨_, rfl⟩
        have hS : E ≤ (Cfg.toData ⟨.ev (.var i), env, kont⟩).size := by
          rw [hE]
          simp only [Cfg.toData, Ctrl.toData, evD, Prog.toData, Data.size_cons, Data.size_nil,
            Data.size_ofNat]
          omega
        refine le_trans ?_ (stepCostBound_mono hS)
        have h1 : ((Data.ofNat i).size + 1) * ((Data.list env).size + (Data.ofNat i).size + 12) ≤
            (E + 1) * (2 * E + 12) := Nat.mul_le_mul (by omega) (by omega)
        have h2 : (w.size + 1) * (5 * w.size + 20) ≤ (E + 1) * (5 * E + 20) :=
          Nat.mul_le_mul (by omega) (by omega)
        have h3 : (E + 1) * (7 * E + 32) = (E + 1) * (2 * E + 12) + (E + 1) * (5 * E + 20) := by
          ring
        unfold stepCostBound
        try simp only [Data.size_cons, Data.size_ofNat] at hs hts htg h1 hE ⊢
        omega
      · have hval : stepCost ⟨.ev (.var i), env, kont⟩ = w.size + 1 := by
          simp only [stepCost, hw, Data.unaryToNat_ofNat, Data.getList_list]
        rw [hval]
        simpa [Prog.Runs, Cfg.toData, Ctrl.toData, evD, Prog.toData] using run
    | nil =>
      obtain ⟨s, hs, run⟩ := stepCostProg_ev 1 .nil (.list env) (.list (kont.map Frame.toData))
        _ (by simp [costCases]) (Eval.const _ (.ofNat 1))
      refine ⟨s, ?_, by simpa [Prog.Runs, Cfg.toData, Ctrl.toData, evD, Prog.toData, stepCost]
        using run⟩
      unfold stepCostBound
      try simp only [Cfg.toData, Ctrl.toData, evD, Prog.toData, Data.size_cons, Data.size_nil,
        Data.size_ofNat] at hs ⊢
      omega
    | const d =>
      obtain ⟨ts, hts, hsz⟩ := sizeProg_runs d
      have hcase : Eval [Data.cons d (.list env)] (costCases.getD 6 .nil) (.ofNat d.size) _ :=
        Eval.elim_cons (i := 0) (a := d) (b := .list env) (by simp)
          (callVar_eval (i := 0) sizeProg_wellScoped (v := d) (by simp) hsz)
      obtain ⟨s, hs, run⟩ := stepCostProg_ev 6 d (.list env) (.list (kont.map Frame.toData))
        _ (by simp [costCases]) hcase
      refine ⟨s, ?_, by simpa [Prog.Runs, Cfg.toData, Ctrl.toData, evD, Prog.toData, stepCost]
        using run⟩
      obtain ⟨E, hE⟩ : ∃ E, E = d.size + (Data.list env).size +
        (Data.list (kont.map Frame.toData)).size + 18 := ⟨_, rfl⟩
      have hS : E ≤ (Cfg.toData ⟨.ev (.const d), env, kont⟩).size := by
        rw [hE]
        simp only [Cfg.toData, Ctrl.toData, evD, Prog.toData, Data.size_cons, Data.size_nil,
          Data.size_ofNat]
        omega
      refine le_trans ?_ (stepCostBound_mono hS)
      have h2 : (d.size + 1) * (5 * d.size + 20) ≤ (E + 1) * (7 * E + 32) :=
        Nat.mul_le_mul (by omega) (by omega)
      unfold stepCostBound
      try simp only [Data.size_cons, Data.size_ofNat] at hs hts ⊢
      omega
    | cons h t =>
      obtain ⟨s, hs, run⟩ := stepCostProg_ev 2 (.cons h.toData t.toData) (.list env)
        (.list (kont.map Frame.toData)) _ (by simp [costCases]) (Eval.const _ (.ofNat 1))
      refine ⟨s, ?_, by simpa [Prog.Runs, Cfg.toData, Ctrl.toData, evD, Prog.toData, stepCost]
        using run⟩
      unfold stepCostBound
      try simp only [Cfg.toData, Ctrl.toData, evD, Prog.toData, Data.size_cons, Data.size_nil,
        Data.size_ofNat] at hs ⊢
      omega
    | elim i n c =>
      obtain ⟨s, hs, run⟩ := stepCostProg_ev 3 (.cons (.ofNat i) (.cons n.toData c.toData))
        (.list env) (.list (kont.map Frame.toData)) _ (by simp [costCases])
        (Eval.const _ (.ofNat 1))
      refine ⟨s, ?_, by simpa [Prog.Runs, Cfg.toData, Ctrl.toData, evD, Prog.toData, stepCost]
        using run⟩
      unfold stepCostBound
      try simp only [Cfg.toData, Ctrl.toData, evD, Prog.toData, Data.size_cons, Data.size_nil,
        Data.size_ofNat] at hs ⊢
      omega
    | let_ e b =>
      obtain ⟨s, hs, run⟩ := stepCostProg_ev 4 (.cons e.toData b.toData) (.list env)
        (.list (kont.map Frame.toData)) _ (by simp [costCases]) (Eval.const _ (.ofNat 1))
      refine ⟨s, ?_, by simpa [Prog.Runs, Cfg.toData, Ctrl.toData, evD, Prog.toData, stepCost]
        using run⟩
      unfold stepCostBound
      try simp only [Cfg.toData, Ctrl.toData, evD, Prog.toData, Data.size_cons, Data.size_nil,
        Data.size_ofNat] at hs ⊢
      omega
    | loop b =>
      obtain ⟨s, hs, run⟩ := stepCostProg_ev 5 b.toData (.list env)
        (.list (kont.map Frame.toData)) _ (by simp [costCases]) (Eval.nil _)
      refine ⟨s, ?_, by simpa [Prog.Runs, Cfg.toData, Ctrl.toData, evD, Prog.toData, stepCost,
        Data.ofNat] using run⟩
      unfold stepCostBound
      try simp only [Cfg.toData, Ctrl.toData, evD, Prog.toData, Data.size_cons, Data.size_nil,
        Data.size_ofNat] at hs ⊢
      omega
  | ret v =>
    cases kont with
    | nil =>
      have run : Eval [Cfg.toData ⟨.ret v, env, []⟩] stepCostProg .nil _ :=
        Eval.elim_cons (i := 0) (a := retD v) (b := .cons (.list env) .nil)
          (by simp [Cfg.toData, Ctrl.toData])
          (Eval.elim_cons (i := 0) (a := .cons .nil .nil) (b := v) (by simp [retD])
            (Eval.elim_cons (i := 0) (a := .nil) (b := .nil) (by simp)
              (Eval.elim_cons (i := 5) (a := .list env) (b := .nil) (by simp)
                (Eval.elim_nil (i := 1) (by simp) (Eval.nil _)))))
      refine ⟨_, ?_, by simpa [Prog.Runs, stepCost, Data.ofNat] using run⟩
      unfold stepCostBound
      omega
    | cons f k =>
      cases f with
      | cons1 t env' =>
        have run : Eval [Cfg.toData ⟨.ret v, env, .cons1 t env' :: k⟩] stepCostProg .nil _ :=
          Eval.elim_cons (i := 0) (a := retD v)
            (b := .cons (.list env) (.cons (Frame.toData (.cons1 t env'))
              (.list (k.map Frame.toData)))) (by simp [Cfg.toData, Ctrl.toData])
            (Eval.elim_cons (i := 0) (a := .cons .nil .nil) (b := v) (by simp [retD])
              (Eval.elim_cons (i := 0) (a := .nil) (b := .nil) (by simp)
                (Eval.elim_cons (i := 5) (a := .list env)
                  (b := .cons (Frame.toData (.cons1 t env')) (.list (k.map Frame.toData)))
                  (by simp)
                  (Eval.elim_cons (i := 1) (a := Frame.toData (.cons1 t env'))
                    (b := .list (k.map Frame.toData)) (by simp)
                    (Eval.elim_cons (i := 0) (a := .ofNat 0) (b := .cons t.toData (.list env'))
                      (by simp [Frame.toData])
                      (Eval.elim_nil (i := 0) (by simp [Data.ofNat]) (Eval.nil _)))))))
        refine ⟨_, ?_, by simpa [Prog.Runs, stepCost, Data.ofNat] using run⟩
        unfold stepCostBound
        omega
      | cons2 a =>
        have run : Eval [Cfg.toData ⟨.ret v, env, .cons2 a :: k⟩] stepCostProg .nil _ :=
          Eval.elim_cons (i := 0) (a := retD v)
            (b := .cons (.list env) (.cons (Frame.toData (.cons2 a))
              (.list (k.map Frame.toData)))) (by simp [Cfg.toData, Ctrl.toData])
            (Eval.elim_cons (i := 0) (a := .cons .nil .nil) (b := v) (by simp [retD])
              (Eval.elim_cons (i := 0) (a := .nil) (b := .nil) (by simp)
                (Eval.elim_cons (i := 5) (a := .list env)
                  (b := .cons (Frame.toData (.cons2 a)) (.list (k.map Frame.toData))) (by simp)
                  (Eval.elim_cons (i := 1) (a := Frame.toData (.cons2 a))
                    (b := .list (k.map Frame.toData)) (by simp)
                    (Eval.elim_cons (i := 0) (a := .ofNat 1) (b := a) (by simp [Frame.toData])
                      (Eval.elim_cons (i := 0) (a := .nil) (b := .ofNat 0) (by simp [Data.ofNat])
                        (Eval.elim_nil (i := 1) (by simp [Data.ofNat]) (Eval.nil _))))))))
        refine ⟨_, ?_, by simpa [Prog.Runs, stepCost, Data.ofNat] using run⟩
        unfold stepCostBound
        omega
      | let1 b env' =>
        have run : Eval [Cfg.toData ⟨.ret v, env, .let1 b env' :: k⟩] stepCostProg .nil _ :=
          Eval.elim_cons (i := 0) (a := retD v)
            (b := .cons (.list env) (.cons (Frame.toData (.let1 b env'))
              (.list (k.map Frame.toData)))) (by simp [Cfg.toData, Ctrl.toData])
            (Eval.elim_cons (i := 0) (a := .cons .nil .nil) (b := v) (by simp [retD])
              (Eval.elim_cons (i := 0) (a := .nil) (b := .nil) (by simp)
                (Eval.elim_cons (i := 5) (a := .list env)
                  (b := .cons (Frame.toData (.let1 b env')) (.list (k.map Frame.toData)))
                  (by simp)
                  (Eval.elim_cons (i := 1) (a := Frame.toData (.let1 b env'))
                    (b := .list (k.map Frame.toData)) (by simp)
                    (Eval.elim_cons (i := 0) (a := .ofNat 2) (b := .cons b.toData (.list env'))
                      (by simp [Frame.toData])
                      (Eval.elim_cons (i := 0) (a := .nil) (b := .ofNat 1) (by simp [Data.ofNat])
                        (Eval.elim_cons (i := 1) (a := .nil) (b := .ofNat 0)
                          (by simp [Data.ofNat])
                          (Eval.elim_nil (i := 1) (by simp [Data.ofNat]) (Eval.nil _)))))))))
        refine ⟨_, ?_, by simpa [Prog.Runs, stepCost, Data.ofNat] using run⟩
        unfold stepCostBound
        omega
      | loop1 b env' =>
        have run : Eval [Cfg.toData ⟨.ret v, env, .loop1 b env' :: k⟩] stepCostProg
            (.ofNat 1) _ :=
          Eval.elim_cons (i := 0) (a := retD v)
            (b := .cons (.list env) (.cons (Frame.toData (.loop1 b env'))
              (.list (k.map Frame.toData)))) (by simp [Cfg.toData, Ctrl.toData])
            (Eval.elim_cons (i := 0) (a := .cons .nil .nil) (b := v) (by simp [retD])
              (Eval.elim_cons (i := 0) (a := .nil) (b := .nil) (by simp)
                (Eval.elim_cons (i := 5) (a := .list env)
                  (b := .cons (Frame.toData (.loop1 b env')) (.list (k.map Frame.toData)))
                  (by simp)
                  (Eval.elim_cons (i := 1) (a := Frame.toData (.loop1 b env'))
                    (b := .list (k.map Frame.toData)) (by simp)
                    (Eval.elim_cons (i := 0) (a := .ofNat 3) (b := .cons b.toData (.list env'))
                      (by simp [Frame.toData])
                      (Eval.elim_cons (i := 0) (a := .nil) (b := .ofNat 2) (by simp [Data.ofNat])
                        (Eval.elim_cons (i := 1) (a := .nil) (b := .ofNat 1)
                          (by simp [Data.ofNat])
                          (Eval.elim_cons (i := 1) (a := .nil) (b := .ofNat 0)
                            (by simp [Data.ofNat]) (Eval.const _ (.ofNat 1))))))))))
        refine ⟨_, ?_, by simpa [Prog.Runs, stepCost] using run⟩
        unfold stepCostBound
        try simp only [Data.size_ofNat]
        omega
