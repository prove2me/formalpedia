-- Prove2me | solution 1 for MIPRE.Cost.Machine.stepEvProg_runs
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-12T16:42:43.229513+00:00
-- url     : https://prove2.me/submissions/5e46368a-483b-4110-996a-d5de1b93c753

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/Interpreter.lean (solution of MIPRE.Cost.Machine.stepEvProg_runs);
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
import Theorems.Thm_MIPRE_Cost_Machine_dispatch_runs
import Theorems.Thm_MIPRE_Cost_Machine_getListProg_runs

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context; each is used only by proofs. -/
namespace MIPRE.Cost.Prog
theorem esize_eq_size_toData (p : Prog) : esize p = p.toData.size := rfl
end MIPRE.Cost.Prog

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
theorem evVar_runs (body env kont : Data) :
    ∃ s ≤ (body.size + 1) * (env.size + body.size + 12) + 4 * env.size + 3 * body.size +
      2 * kont.size + 20,
      Eval [Data.cons body (.cons env kont)] evVar
        (.cons (retD (Data.getList env (Data.unaryToNat body))) (.cons env kont)) s := by
  obtain ⟨t, ht, hg⟩ := getListProg_runs body env []
  have hv := size_getList_le env (Data.unaryToNat body)
  have run : Eval [Data.cons body (.cons env kont)] evVar
      (.cons (retD (Data.getList env (Data.unaryToNat body))) (.cons env kont)) _ :=
    Eval.elim_cons (i := 0) (a := body) (b := .cons env kont) (by simp)
    (Eval.elim_cons (i := 1) (a := env) (b := kont) (by simp)
      (Eval.let_ (Eval.cons (Eval.var_of_get (i := 0) (v := env) (by simp))
          (Eval.var_of_get (i := 2) (v := body) (by simp)))
        (Eval.let_ (callVar_eval (i := 0) getListProg_wellScoped (v := .cons env body) (by simp) hg)
          (Eval.cons (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _))
              (Eval.var_of_get (i := 0) (v := Data.getList env (Data.unaryToNat body)) (by simp)))
            (Eval.var_of_get (i := 5) (v := .cons env kont) (by simp))))))
  refine ⟨_, ?_, run⟩
  ((try simp only [MIPRE.Cost.Data.size_cons, MIPRE.Cost.Data.size_nil, MIPRE.Cost.Data.size_ofNat, MIPRE.Cost.Machine.Frame.toData, MIPRE.Cost.Machine.Cfg.toData, MIPRE.Cost.Machine.Ctrl.toData, MIPRE.Cost.Machine.evD, MIPRE.Cost.Machine.retD, MIPRE.Cost.Prog.toData, MIPRE.Cost.Data.list_cons, MIPRE.Cost.Data.list_nil, List.map_cons, List.map_nil] at *); all_goals omega)
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Prog
theorem evNil_runs (body env kont : Data) :
    ∃ s ≤ env.size + kont.size + 12,
      Eval [Data.cons body (.cons env kont)] evNil (.cons (retD .nil) (.cons env kont)) s := by
  have run : Eval [Data.cons body (.cons env kont)] evNil (.cons (retD .nil) (.cons env kont)) _ :=
    Eval.elim_cons (i := 0) (a := body) (b := .cons env kont) (by simp)
    (Eval.elim_cons (i := 1) (a := env) (b := kont) (by simp)
      (Eval.cons (Eval.const _ (.cons (.cons .nil .nil) .nil))
        (Eval.var_of_get (i := 3) (v := .cons env kont) (by simp))))
  refine ⟨_, ?_, run⟩
  ((try simp only [MIPRE.Cost.Data.size_cons, MIPRE.Cost.Data.size_nil, MIPRE.Cost.Data.size_ofNat, MIPRE.Cost.Machine.Frame.toData, MIPRE.Cost.Machine.Cfg.toData, MIPRE.Cost.Machine.Ctrl.toData, MIPRE.Cost.Machine.evD, MIPRE.Cost.Machine.retD, MIPRE.Cost.Prog.toData, MIPRE.Cost.Data.list_cons, MIPRE.Cost.Data.list_nil, List.map_cons, List.map_nil] at *); all_goals omega)
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Prog
theorem evCons_runs (h t env kont : Data) :
    ∃ s ≤ h.size + t.size + 2 * env.size + kont.size + 20,
      Eval [Data.cons (.cons h t) (.cons env kont)] evCons
        (.cons (evD h) (.cons env (.cons (.cons (.ofNat 0) (.cons t env)) kont))) s := by
  have run : Eval [Data.cons (.cons h t) (.cons env kont)] evCons
      (.cons (evD h) (.cons env (.cons (.cons (.ofNat 0) (.cons t env)) kont))) _ :=
    Eval.elim_cons (i := 0) (a := .cons h t) (b := .cons env kont) (by simp)
    (Eval.elim_cons (i := 1) (a := env) (b := kont) (by simp)
      (Eval.elim_cons (i := 2) (a := h) (b := t) (by simp)
        (Eval.cons (Eval.cons (Eval.nil _) (Eval.var_of_get (i := 0) (v := h) (by simp)))
          (Eval.cons (Eval.var_of_get (i := 2) (v := env) (by simp))
            (Eval.cons (Eval.cons (Eval.const _ (.ofNat 0))
                (Eval.cons (Eval.var_of_get (i := 1) (v := t) (by simp))
                  (Eval.var_of_get (i := 2) (v := env) (by simp))))
              (Eval.var_of_get (i := 3) (v := kont) (by simp)))))))
  refine ⟨_, ?_, run⟩
  ((try simp only [MIPRE.Cost.Data.size_cons, MIPRE.Cost.Data.size_nil, MIPRE.Cost.Data.size_ofNat, MIPRE.Cost.Machine.Frame.toData, MIPRE.Cost.Machine.Cfg.toData, MIPRE.Cost.Machine.Ctrl.toData, MIPRE.Cost.Machine.evD, MIPRE.Cost.Machine.retD, MIPRE.Cost.Prog.toData, MIPRE.Cost.Data.list_cons, MIPRE.Cost.Data.list_nil, List.map_cons, List.map_nil] at *); all_goals omega)
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Prog
theorem evLet_runs (e b env kont : Data) :
    ∃ s ≤ e.size + b.size + 2 * env.size + kont.size + 24,
      Eval [Data.cons (.cons e b) (.cons env kont)] evLet
        (.cons (evD e) (.cons env (.cons (.cons (.ofNat 2) (.cons b env)) kont))) s := by
  have run : Eval [Data.cons (.cons e b) (.cons env kont)] evLet
      (.cons (evD e) (.cons env (.cons (.cons (.ofNat 2) (.cons b env)) kont))) _ :=
    Eval.elim_cons (i := 0) (a := .cons e b) (b := .cons env kont) (by simp)
    (Eval.elim_cons (i := 1) (a := env) (b := kont) (by simp)
      (Eval.elim_cons (i := 2) (a := e) (b := b) (by simp)
        (Eval.cons (Eval.cons (Eval.nil _) (Eval.var_of_get (i := 0) (v := e) (by simp)))
          (Eval.cons (Eval.var_of_get (i := 2) (v := env) (by simp))
            (Eval.cons (Eval.cons (Eval.const _ (.ofNat 2))
                (Eval.cons (Eval.var_of_get (i := 1) (v := b) (by simp))
                  (Eval.var_of_get (i := 2) (v := env) (by simp))))
              (Eval.var_of_get (i := 3) (v := kont) (by simp)))))))
  refine ⟨_, ?_, run⟩
  ((try simp only [MIPRE.Cost.Data.size_cons, MIPRE.Cost.Data.size_nil, MIPRE.Cost.Data.size_ofNat, MIPRE.Cost.Machine.Frame.toData, MIPRE.Cost.Machine.Cfg.toData, MIPRE.Cost.Machine.Ctrl.toData, MIPRE.Cost.Machine.evD, MIPRE.Cost.Machine.retD, MIPRE.Cost.Prog.toData, MIPRE.Cost.Data.list_cons, MIPRE.Cost.Data.list_nil, List.map_cons, List.map_nil] at *); all_goals omega)
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Prog
theorem evLoop_runs (b env kont : Data) :
    ∃ s ≤ 2 * b.size + 2 * env.size + kont.size + 26,
      Eval [Data.cons b (.cons env kont)] evLoop
        (.cons (evD b) (.cons env (.cons (.cons (.ofNat 3) (.cons b env)) kont))) s := by
  have run : Eval [Data.cons b (.cons env kont)] evLoop
      (.cons (evD b) (.cons env (.cons (.cons (.ofNat 3) (.cons b env)) kont))) _ :=
    Eval.elim_cons (i := 0) (a := b) (b := .cons env kont) (by simp)
    (Eval.elim_cons (i := 1) (a := env) (b := kont) (by simp)
      (Eval.cons (Eval.cons (Eval.nil _) (Eval.var_of_get (i := 2) (v := b) (by simp)))
        (Eval.cons (Eval.var_of_get (i := 0) (v := env) (by simp))
          (Eval.cons (Eval.cons (Eval.const _ (.ofNat 3))
              (Eval.cons (Eval.var_of_get (i := 2) (v := b) (by simp))
                (Eval.var_of_get (i := 0) (v := env) (by simp))))
            (Eval.var_of_get (i := 1) (v := kont) (by simp))))))
  refine ⟨_, ?_, run⟩
  ((try simp only [MIPRE.Cost.Data.size_cons, MIPRE.Cost.Data.size_nil, MIPRE.Cost.Data.size_ofNat, MIPRE.Cost.Machine.Frame.toData, MIPRE.Cost.Machine.Cfg.toData, MIPRE.Cost.Machine.Ctrl.toData, MIPRE.Cost.Machine.evD, MIPRE.Cost.Machine.retD, MIPRE.Cost.Prog.toData, MIPRE.Cost.Data.list_cons, MIPRE.Cost.Data.list_nil, List.map_cons, List.map_nil] at *); all_goals omega)
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Prog
theorem evConst_runs (d env kont : Data) :
    ∃ s ≤ d.size + env.size + kont.size + 12,
      Eval [Data.cons d (.cons env kont)] evConst (.cons (retD d) (.cons env kont)) s := by
  have run : Eval [Data.cons d (.cons env kont)] evConst (.cons (retD d) (.cons env kont)) _ :=
    Eval.elim_cons (i := 0) (a := d) (b := .cons env kont) (by simp)
    (Eval.elim_cons (i := 1) (a := env) (b := kont) (by simp)
      (Eval.cons (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _))
          (Eval.var_of_get (i := 2) (v := d) (by simp)))
        (Eval.var_of_get (i := 3) (v := .cons env kont) (by simp))))
  refine ⟨_, ?_, run⟩
  ((try simp only [MIPRE.Cost.Data.size_cons, MIPRE.Cost.Data.size_nil, MIPRE.Cost.Data.size_ofNat, MIPRE.Cost.Machine.Frame.toData, MIPRE.Cost.Machine.Cfg.toData, MIPRE.Cost.Machine.Ctrl.toData, MIPRE.Cost.Machine.evD, MIPRE.Cost.Machine.retD, MIPRE.Cost.Prog.toData, MIPRE.Cost.Data.list_cons, MIPRE.Cost.Data.list_nil, List.map_cons, List.map_nil] at *); all_goals omega)
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Prog
theorem evElim_runs (i n c env kont : Data) :
    ∃ s ≤ (i.size + 1) * (env.size + i.size + 12) + 5 * env.size + 3 * i.size + n.size + c.size +
      2 * kont.size + 40,
      Eval [Data.cons (.cons i (.cons n c)) (.cons env kont)] evElim
        (if Data.getList env (Data.unaryToNat i) = .nil then .cons (evD n) (.cons env kont)
        else .cons (evD c) (.cons (.cons (Data.getList env (Data.unaryToNat i)).left
          (.cons (Data.getList env (Data.unaryToNat i)).right env)) kont)) s := by
  obtain ⟨t, ht, hg⟩ := getListProg_runs i env []
  have hv := size_getList_le env (Data.unaryToNat i)
  rcases hget : Data.getList env (Data.unaryToNat i) with _ | ⟨a, b⟩
  · rw [hget] at hg
    have run : Eval [Data.cons (.cons i (.cons n c)) (.cons env kont)] evElim
        (.cons (evD n) (.cons env kont)) _ :=
      Eval.elim_cons (i := 0) (a := .cons i (.cons n c)) (b := .cons env kont) (by simp)
        (Eval.elim_cons (i := 1) (a := env) (b := kont) (by simp)
          (Eval.elim_cons (i := 2) (a := i) (b := .cons n c) (by simp)
            (Eval.elim_cons (i := 1) (a := n) (b := c) (by simp)
              (Eval.let_ (Eval.cons (Eval.var_of_get (i := 4) (v := env) (by simp))
                  (Eval.var_of_get (i := 2) (v := i) (by simp)))
                (Eval.let_ (callVar_eval (i := 0) getListProg_wellScoped (v := .cons env i)
                    (by simp) hg)
                  (Eval.elim_nil (i := 0) (by simp)
                    (Eval.cons (Eval.cons (Eval.nil _) (Eval.var_of_get (i := 2) (v := n) (by simp)))
                      (Eval.var_of_get (i := 9) (v := .cons env kont) (by simp)))))))))
    refine ⟨_, ?_, run⟩
    ((try simp only [MIPRE.Cost.Data.size_cons, MIPRE.Cost.Data.size_nil, MIPRE.Cost.Data.size_ofNat, MIPRE.Cost.Machine.Frame.toData, MIPRE.Cost.Machine.Cfg.toData, MIPRE.Cost.Machine.Ctrl.toData, MIPRE.Cost.Machine.evD, MIPRE.Cost.Machine.retD, MIPRE.Cost.Prog.toData, MIPRE.Cost.Data.list_cons, MIPRE.Cost.Data.list_nil, List.map_cons, List.map_nil] at *); all_goals omega)
  · rw [hget] at hg hv
    have run : Eval [Data.cons (.cons i (.cons n c)) (.cons env kont)] evElim
        (.cons (evD c) (.cons (.cons a (.cons b env)) kont)) _ :=
      Eval.elim_cons (i := 0) (a := .cons i (.cons n c)) (b := .cons env kont) (by simp)
        (Eval.elim_cons (i := 1) (a := env) (b := kont) (by simp)
          (Eval.elim_cons (i := 2) (a := i) (b := .cons n c) (by simp)
            (Eval.elim_cons (i := 1) (a := n) (b := c) (by simp)
              (Eval.let_ (Eval.cons (Eval.var_of_get (i := 4) (v := env) (by simp))
                  (Eval.var_of_get (i := 2) (v := i) (by simp)))
                (Eval.let_ (callVar_eval (i := 0) getListProg_wellScoped (v := .cons env i)
                    (by simp) hg)
                  (Eval.elim_cons (i := 0) (a := a) (b := b) (by simp)
                    (Eval.cons (Eval.cons (Eval.nil _) (Eval.var_of_get (i := 5) (v := c) (by simp)))
                      (Eval.cons (Eval.cons (Eval.var_of_get (i := 0) (v := a) (by simp))
                          (Eval.cons (Eval.var_of_get (i := 1) (v := b) (by simp))
                            (Eval.var_of_get (i := 8) (v := env) (by simp))))
                        (Eval.var_of_get (i := 9) (v := kont) (by simp))))))))))
    refine ⟨_, ?_, run⟩
    ((try simp only [MIPRE.Cost.Data.size_cons, MIPRE.Cost.Data.size_nil, MIPRE.Cost.Data.size_ofNat, MIPRE.Cost.Machine.Frame.toData, MIPRE.Cost.Machine.Cfg.toData, MIPRE.Cost.Machine.Ctrl.toData, MIPRE.Cost.Machine.evD, MIPRE.Cost.Machine.retD, MIPRE.Cost.Prog.toData, MIPRE.Cost.Data.list_cons, MIPRE.Cost.Data.list_nil, List.map_cons, List.map_nil] at *); all_goals omega)
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
/-- The prefix of `stepEvProg` up to the dispatch. -/
theorem stepEvProg_prefix (k : ℕ) (body env kont r : Data) {s : ℕ}
    (hd : Eval (dispEnv k body env kont) (dispatch evCases 0 1) r s) :
    ∃ c ≤ s + body.size + env.size + kont.size + (Data.ofNat k).size + 12,
      Eval [Data.cons (.cons (.ofNat k) body) (.cons env kont)] stepEvProg r c := by
  have run : Eval [Data.cons (.cons (.ofNat k) body) (.cons env kont)] stepEvProg r _ :=
    Eval.elim_cons (i := 0) (a := .cons (.ofNat k) body) (b := .cons env kont) (by simp)
      (Eval.elim_cons (i := 1) (a := env) (b := kont) (by simp)
        (Eval.elim_cons (i := 2) (a := .ofNat k) (b := body) (by simp)
          (Eval.let_ (Eval.cons (Eval.var_of_get (i := 1) (v := body) (by simp))
              (Eval.cons (Eval.var_of_get (i := 2) (v := env) (by simp))
                (Eval.var_of_get (i := 3) (v := kont) (by simp))))
            (Eval.let_ (Eval.var_of_get (i := 1) (v := .ofNat k) (by simp)) hd))))
  exact ⟨_, by omega, run⟩
end MIPRE.Cost.Machine

/-! The uploaded declaration, hoisted to the top level as `solution`. -/
open MIPRE
open MIPRE.Cost
open MIPRE.Cost.Machine
open MIPRE.Cost.Prog
theorem solution (p : Prog) (env kont : Data) :
    ∃ s ≤ stepEvBound (esize p + env.size + kont.size),
      stepEvProg.Runs (.cons p.toData (.cons env kont)) (stepEv p.toData env kont) s := by
  have hsplit : ∀ S : ℕ, stepEvBound S = (S + 1) * (S + 12) + 18 * (S + 1) + 100 := fun S => by
    unfold stepEvBound; ring
  cases p with
  | var i =>
    obtain ⟨c₀, hc₀, hcase⟩ := evVar_runs (.ofNat i) env kont
    obtain ⟨s, hs, hd⟩ := dispatch_runs evCases 0 0 1 (dispEnv 0 (.ofNat i) env kont)
      (Data.cons (.ofNat i) (.cons env kont)) _ c₀ (by simp [evCases]) evCases_wellScoped
      (by simp [dispEnv]) (by simp [dispEnv])
      (show Eval [Data.cons (.ofNat i) (.cons env kont)] (evCases.getD 0 .nil) _ _ from hcase)
    obtain ⟨c', hc', run⟩ := stepEvProg_prefix 0 (.ofNat i) env kont _ hd
    refine ⟨_, ?_, by simpa [Prog.Runs, stepEv, Prog.toData] using run⟩
    have hE : esize (Prog.var i) = 2 * i + 3 := by
      simp only [Prog.esize_eq_size_toData]; ((try simp only [MIPRE.Cost.Data.size_cons, MIPRE.Cost.Data.size_nil, MIPRE.Cost.Data.size_ofNat, MIPRE.Cost.Machine.Frame.toData, MIPRE.Cost.Machine.Cfg.toData, MIPRE.Cost.Machine.Ctrl.toData, MIPRE.Cost.Machine.evD, MIPRE.Cost.Machine.retD, MIPRE.Cost.Prog.toData, MIPRE.Cost.Data.list_cons, MIPRE.Cost.Data.list_nil, List.map_cons, List.map_nil] at *); all_goals omega)
    rw [hsplit, hE]
    simp only [Data.size_ofNat, Data.size_cons] at hc₀ hs hc' ⊢
    have hq : (2 * i + 1 + 1) * (env.size + (2 * i + 1) + 12) ≤
        (2 * i + 3 + env.size + kont.size + 1) * (2 * i + 3 + env.size + kont.size + 12) :=
      Nat.mul_le_mul (by omega) (by omega)
    omega
  | nil =>
    obtain ⟨c₀, hc₀, hcase⟩ := evNil_runs .nil env kont
    obtain ⟨s, hs, hd⟩ := dispatch_runs evCases 1 0 1 (dispEnv 1 .nil env kont)
      (Data.cons .nil (.cons env kont)) _ c₀ (by simp [evCases]) evCases_wellScoped
      (by simp [dispEnv]) (by simp [dispEnv])
      (show Eval [Data.cons .nil (.cons env kont)] (evCases.getD 1 .nil) _ _ from hcase)
    obtain ⟨c', hc', run⟩ := stepEvProg_prefix 1 .nil env kont _ hd
    refine ⟨_, ?_, by simpa [Prog.Runs, stepEv, Prog.toData] using run⟩
    have hE : esize Prog.nil = 5 := by
      simp only [Prog.esize_eq_size_toData]; ((try simp only [MIPRE.Cost.Data.size_cons, MIPRE.Cost.Data.size_nil, MIPRE.Cost.Data.size_ofNat, MIPRE.Cost.Machine.Frame.toData, MIPRE.Cost.Machine.Cfg.toData, MIPRE.Cost.Machine.Ctrl.toData, MIPRE.Cost.Machine.evD, MIPRE.Cost.Machine.retD, MIPRE.Cost.Prog.toData, MIPRE.Cost.Data.list_cons, MIPRE.Cost.Data.list_nil, List.map_cons, List.map_nil] at *); all_goals omega)
    rw [hsplit, hE]
    ((try simp only [MIPRE.Cost.Data.size_cons, MIPRE.Cost.Data.size_nil, MIPRE.Cost.Data.size_ofNat, MIPRE.Cost.Machine.Frame.toData, MIPRE.Cost.Machine.Cfg.toData, MIPRE.Cost.Machine.Ctrl.toData, MIPRE.Cost.Machine.evD, MIPRE.Cost.Machine.retD, MIPRE.Cost.Prog.toData, MIPRE.Cost.Data.list_cons, MIPRE.Cost.Data.list_nil, List.map_cons, List.map_nil] at *); all_goals omega)
  | cons h t =>
    obtain ⟨c₀, hc₀, hcase⟩ := evCons_runs h.toData t.toData env kont
    obtain ⟨s, hs, hd⟩ := dispatch_runs evCases 2 0 1 (dispEnv 2 (.cons h.toData t.toData) env kont)
      (Data.cons (.cons h.toData t.toData) (.cons env kont)) _ c₀ (by simp [evCases]) evCases_wellScoped
      (by simp [dispEnv]) (by simp [dispEnv])
      (show Eval [Data.cons (.cons h.toData t.toData) (.cons env kont)] (evCases.getD 2 .nil) _ _ from hcase)
    obtain ⟨c', hc', run⟩ := stepEvProg_prefix 2 (.cons h.toData t.toData) env kont _ hd
    refine ⟨_, ?_, by simpa [Prog.Runs, stepEv, Prog.toData] using run⟩
    have hE : esize (Prog.cons h t) = esize h + esize t + 7 := by
      simp only [Prog.esize_eq_size_toData]; ((try simp only [MIPRE.Cost.Data.size_cons, MIPRE.Cost.Data.size_nil, MIPRE.Cost.Data.size_ofNat, MIPRE.Cost.Machine.Frame.toData, MIPRE.Cost.Machine.Cfg.toData, MIPRE.Cost.Machine.Ctrl.toData, MIPRE.Cost.Machine.evD, MIPRE.Cost.Machine.retD, MIPRE.Cost.Prog.toData, MIPRE.Cost.Data.list_cons, MIPRE.Cost.Data.list_nil, List.map_cons, List.map_nil] at *); all_goals omega)
    have h_h : h.toData.size = esize h := rfl
    have h_t : t.toData.size = esize t := rfl
    rw [hsplit, hE]
    ((try simp only [MIPRE.Cost.Data.size_cons, MIPRE.Cost.Data.size_nil, MIPRE.Cost.Data.size_ofNat, MIPRE.Cost.Machine.Frame.toData, MIPRE.Cost.Machine.Cfg.toData, MIPRE.Cost.Machine.Ctrl.toData, MIPRE.Cost.Machine.evD, MIPRE.Cost.Machine.retD, MIPRE.Cost.Prog.toData, MIPRE.Cost.Data.list_cons, MIPRE.Cost.Data.list_nil, List.map_cons, List.map_nil] at *); all_goals omega)
  | elim i n c =>
    obtain ⟨c₀, hc₀, hcase⟩ := evElim_runs (.ofNat i) n.toData c.toData env kont
    obtain ⟨s, hs, hd⟩ := dispatch_runs evCases 3 0 1 (dispEnv 3 (.cons (.ofNat i) (.cons n.toData c.toData)) env kont)
      (Data.cons (.cons (.ofNat i) (.cons n.toData c.toData)) (.cons env kont)) _ c₀ (by simp [evCases]) evCases_wellScoped
      (by simp [dispEnv]) (by simp [dispEnv])
      (show Eval [Data.cons (.cons (.ofNat i) (.cons n.toData c.toData)) (.cons env kont)] (evCases.getD 3 .nil) _ _ from hcase)
    obtain ⟨c', hc', run⟩ := stepEvProg_prefix 3 (.cons (.ofNat i) (.cons n.toData c.toData)) env kont _ hd
    refine ⟨_, ?_, by simpa [Prog.Runs, stepEv, Prog.toData] using run⟩
    have hE : esize (Prog.elim i n c) = 2 * i + esize n + esize c + 11 := by
      simp only [Prog.esize_eq_size_toData]; ((try simp only [MIPRE.Cost.Data.size_cons, MIPRE.Cost.Data.size_nil, MIPRE.Cost.Data.size_ofNat, MIPRE.Cost.Machine.Frame.toData, MIPRE.Cost.Machine.Cfg.toData, MIPRE.Cost.Machine.Ctrl.toData, MIPRE.Cost.Machine.evD, MIPRE.Cost.Machine.retD, MIPRE.Cost.Prog.toData, MIPRE.Cost.Data.list_cons, MIPRE.Cost.Data.list_nil, List.map_cons, List.map_nil] at *); all_goals omega)
    have h_n : n.toData.size = esize n := rfl
    have h_c : c.toData.size = esize c := rfl
    rw [hsplit, hE]
    simp only [Data.size_ofNat, Data.size_cons] at hc₀ hs hc' ⊢
    have hq : (2 * i + 1 + 1) * (env.size + (2 * i + 1) + 12) ≤
        (2 * i + esize n + esize c + 11 + env.size + kont.size + 1) *
          (2 * i + esize n + esize c + 11 + env.size + kont.size + 12) :=
      Nat.mul_le_mul (by omega) (by omega)
    omega
  | let_ e b =>
    obtain ⟨c₀, hc₀, hcase⟩ := evLet_runs e.toData b.toData env kont
    obtain ⟨s, hs, hd⟩ := dispatch_runs evCases 4 0 1 (dispEnv 4 (.cons e.toData b.toData) env kont)
      (Data.cons (.cons e.toData b.toData) (.cons env kont)) _ c₀ (by simp [evCases]) evCases_wellScoped
      (by simp [dispEnv]) (by simp [dispEnv])
      (show Eval [Data.cons (.cons e.toData b.toData) (.cons env kont)] (evCases.getD 4 .nil) _ _ from hcase)
    obtain ⟨c', hc', run⟩ := stepEvProg_prefix 4 (.cons e.toData b.toData) env kont _ hd
    refine ⟨_, ?_, by simpa [Prog.Runs, stepEv, Prog.toData] using run⟩
    have hE : esize (Prog.let_ e b) = esize e + esize b + 11 := by
      simp only [Prog.esize_eq_size_toData]; ((try simp only [MIPRE.Cost.Data.size_cons, MIPRE.Cost.Data.size_nil, MIPRE.Cost.Data.size_ofNat, MIPRE.Cost.Machine.Frame.toData, MIPRE.Cost.Machine.Cfg.toData, MIPRE.Cost.Machine.Ctrl.toData, MIPRE.Cost.Machine.evD, MIPRE.Cost.Machine.retD, MIPRE.Cost.Prog.toData, MIPRE.Cost.Data.list_cons, MIPRE.Cost.Data.list_nil, List.map_cons, List.map_nil] at *); all_goals omega)
    have h_e : e.toData.size = esize e := rfl
    have h_b : b.toData.size = esize b := rfl
    rw [hsplit, hE]
    ((try simp only [MIPRE.Cost.Data.size_cons, MIPRE.Cost.Data.size_nil, MIPRE.Cost.Data.size_ofNat, MIPRE.Cost.Machine.Frame.toData, MIPRE.Cost.Machine.Cfg.toData, MIPRE.Cost.Machine.Ctrl.toData, MIPRE.Cost.Machine.evD, MIPRE.Cost.Machine.retD, MIPRE.Cost.Prog.toData, MIPRE.Cost.Data.list_cons, MIPRE.Cost.Data.list_nil, List.map_cons, List.map_nil] at *); all_goals omega)
  | loop b =>
    obtain ⟨c₀, hc₀, hcase⟩ := evLoop_runs b.toData env kont
    obtain ⟨s, hs, hd⟩ := dispatch_runs evCases 5 0 1 (dispEnv 5 b.toData env kont)
      (Data.cons b.toData (.cons env kont)) _ c₀ (by simp [evCases]) evCases_wellScoped
      (by simp [dispEnv]) (by simp [dispEnv])
      (show Eval [Data.cons b.toData (.cons env kont)] (evCases.getD 5 .nil) _ _ from hcase)
    obtain ⟨c', hc', run⟩ := stepEvProg_prefix 5 b.toData env kont _ hd
    refine ⟨_, ?_, by simpa [Prog.Runs, stepEv, Prog.toData] using run⟩
    have hE : esize (Prog.loop b) = esize b + 12 := by
      simp only [Prog.esize_eq_size_toData]; ((try simp only [MIPRE.Cost.Data.size_cons, MIPRE.Cost.Data.size_nil, MIPRE.Cost.Data.size_ofNat, MIPRE.Cost.Machine.Frame.toData, MIPRE.Cost.Machine.Cfg.toData, MIPRE.Cost.Machine.Ctrl.toData, MIPRE.Cost.Machine.evD, MIPRE.Cost.Machine.retD, MIPRE.Cost.Prog.toData, MIPRE.Cost.Data.list_cons, MIPRE.Cost.Data.list_nil, List.map_cons, List.map_nil] at *); all_goals omega)
    have h_b : b.toData.size = esize b := rfl
    rw [hsplit, hE]
    ((try simp only [MIPRE.Cost.Data.size_cons, MIPRE.Cost.Data.size_nil, MIPRE.Cost.Data.size_ofNat, MIPRE.Cost.Machine.Frame.toData, MIPRE.Cost.Machine.Cfg.toData, MIPRE.Cost.Machine.Ctrl.toData, MIPRE.Cost.Machine.evD, MIPRE.Cost.Machine.retD, MIPRE.Cost.Prog.toData, MIPRE.Cost.Data.list_cons, MIPRE.Cost.Data.list_nil, List.map_cons, List.map_nil] at *); all_goals omega)
  | const d =>
    obtain ⟨c₀, hc₀, hcase⟩ := evConst_runs d env kont
    obtain ⟨s, hs, hd⟩ := dispatch_runs evCases 6 0 1 (dispEnv 6 d env kont)
      (Data.cons d (.cons env kont)) _ c₀ (by simp [evCases]) evCases_wellScoped
      (by simp [dispEnv]) (by simp [dispEnv])
      (show Eval [Data.cons d (.cons env kont)] (evCases.getD 6 .nil) _ _ from hcase)
    obtain ⟨c', hc', run⟩ := stepEvProg_prefix 6 d env kont _ hd
    refine ⟨_, ?_, by simpa [Prog.Runs, stepEv, Prog.toData] using run⟩
    have hE : esize (Prog.const d) = d.size + 14 := by
      simp only [Prog.esize_eq_size_toData]; ((try simp only [MIPRE.Cost.Data.size_cons, MIPRE.Cost.Data.size_nil, MIPRE.Cost.Data.size_ofNat, MIPRE.Cost.Machine.Frame.toData, MIPRE.Cost.Machine.Cfg.toData, MIPRE.Cost.Machine.Ctrl.toData, MIPRE.Cost.Machine.evD, MIPRE.Cost.Machine.retD, MIPRE.Cost.Prog.toData, MIPRE.Cost.Data.list_cons, MIPRE.Cost.Data.list_nil, List.map_cons, List.map_nil] at *); all_goals omega)
    rw [hsplit, hE]
    ((try simp only [MIPRE.Cost.Data.size_cons, MIPRE.Cost.Data.size_nil, MIPRE.Cost.Data.size_ofNat, MIPRE.Cost.Machine.Frame.toData, MIPRE.Cost.Machine.Cfg.toData, MIPRE.Cost.Machine.Ctrl.toData, MIPRE.Cost.Machine.evD, MIPRE.Cost.Machine.retD, MIPRE.Cost.Prog.toData, MIPRE.Cost.Data.list_cons, MIPRE.Cost.Data.list_nil, List.map_cons, List.map_nil] at *); all_goals omega)
