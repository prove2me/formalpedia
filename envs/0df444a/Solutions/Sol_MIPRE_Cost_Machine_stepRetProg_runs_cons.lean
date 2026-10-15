-- Prove2me | solution 1 for MIPRE.Cost.Machine.stepRetProg_runs_cons
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-12T16:43:21.357985+00:00
-- url     : https://prove2.me/submissions/550c6a66-fcd5-40cb-a48b-d2ef0c430b50

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/Interpreter.lean (solution of MIPRE.Cost.Machine.stepRetProg_runs_cons);
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

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context; each is used only by proofs. -/
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
theorem retCons1_runs (t' env' v env k : Data) :
    ∃ s ≤ t'.size + env'.size + v.size + k.size + 20,
      Eval [Data.cons v (.cons env (.cons (.cons t' env') k))] retCons1
        (.cons (evD t') (.cons env' (.cons (.cons (.ofNat 1) v) k))) s := by
  have run : Eval [Data.cons v (.cons env (.cons (.cons t' env') k))] retCons1
      (.cons (evD t') (.cons env' (.cons (.cons (.ofNat 1) v) k))) _ :=
    Eval.elim_cons (i := 0) (a := v) (b := .cons env (.cons (.cons t' env') k)) (by simp)
      (Eval.elim_cons (i := 1) (a := env) (b := .cons (.cons t' env') k) (by simp)
        (Eval.elim_cons (i := 1) (a := .cons t' env') (b := k) (by simp)
          (Eval.elim_cons (i := 0) (a := t') (b := env') (by simp)
            (Eval.cons (Eval.cons (Eval.nil _) (Eval.var_of_get (i := 0) (v := t') (by simp)))
              (Eval.cons (Eval.var_of_get (i := 1) (v := env') (by simp))
                (Eval.cons (Eval.cons (Eval.const _ (.ofNat 1))
                    (Eval.var_of_get (i := 6) (v := v) (by simp)))
                  (Eval.var_of_get (i := 3) (v := k) (by simp))))))))
  refine ⟨_, ?_, run⟩
  ((try simp only [MIPRE.Cost.Data.size_cons, MIPRE.Cost.Data.size_nil, MIPRE.Cost.Data.size_ofNat, MIPRE.Cost.Machine.Frame.toData, MIPRE.Cost.Machine.Cfg.toData, MIPRE.Cost.Machine.Ctrl.toData, MIPRE.Cost.Machine.evD, MIPRE.Cost.Machine.retD, MIPRE.Cost.Prog.toData, MIPRE.Cost.Data.list_cons, MIPRE.Cost.Data.list_nil, List.map_cons, List.map_nil] at *); all_goals omega)
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Prog
theorem retCons2_runs (a v env k : Data) :
    ∃ s ≤ a.size + v.size + env.size + k.size + 16,
      Eval [Data.cons v (.cons env (.cons a k))] retCons2
        (.cons (retD (.cons a v)) (.cons env k)) s := by
  have run : Eval [Data.cons v (.cons env (.cons a k))] retCons2
      (.cons (retD (.cons a v)) (.cons env k)) _ :=
    Eval.elim_cons (i := 0) (a := v) (b := .cons env (.cons a k)) (by simp)
      (Eval.elim_cons (i := 1) (a := env) (b := .cons a k) (by simp)
        (Eval.elim_cons (i := 1) (a := a) (b := k) (by simp)
          (Eval.cons (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _))
              (Eval.cons (Eval.var_of_get (i := 0) (v := a) (by simp))
                (Eval.var_of_get (i := 4) (v := v) (by simp))))
            (Eval.cons (Eval.var_of_get (i := 2) (v := env) (by simp))
              (Eval.var_of_get (i := 1) (v := k) (by simp))))))
  refine ⟨_, ?_, run⟩
  ((try simp only [MIPRE.Cost.Data.size_cons, MIPRE.Cost.Data.size_nil, MIPRE.Cost.Data.size_ofNat, MIPRE.Cost.Machine.Frame.toData, MIPRE.Cost.Machine.Cfg.toData, MIPRE.Cost.Machine.Ctrl.toData, MIPRE.Cost.Machine.evD, MIPRE.Cost.Machine.retD, MIPRE.Cost.Prog.toData, MIPRE.Cost.Data.list_cons, MIPRE.Cost.Data.list_nil, List.map_cons, List.map_nil] at *); all_goals omega)
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Prog
theorem retLet1_runs (b env' v env k : Data) :
    ∃ s ≤ b.size + v.size + env'.size + k.size + 16,
      Eval [Data.cons v (.cons env (.cons (.cons b env') k))] retLet1
        (.cons (evD b) (.cons (.cons v env') k)) s := by
  have run : Eval [Data.cons v (.cons env (.cons (.cons b env') k))] retLet1
      (.cons (evD b) (.cons (.cons v env') k)) _ :=
    Eval.elim_cons (i := 0) (a := v) (b := .cons env (.cons (.cons b env') k)) (by simp)
      (Eval.elim_cons (i := 1) (a := env) (b := .cons (.cons b env') k) (by simp)
        (Eval.elim_cons (i := 1) (a := .cons b env') (b := k) (by simp)
          (Eval.elim_cons (i := 0) (a := b) (b := env') (by simp)
            (Eval.cons (Eval.cons (Eval.nil _) (Eval.var_of_get (i := 0) (v := b) (by simp)))
              (Eval.cons (Eval.cons (Eval.var_of_get (i := 6) (v := v) (by simp))
                  (Eval.var_of_get (i := 1) (v := env') (by simp)))
                (Eval.var_of_get (i := 3) (v := k) (by simp)))))))
  refine ⟨_, ?_, run⟩
  ((try simp only [MIPRE.Cost.Data.size_cons, MIPRE.Cost.Data.size_nil, MIPRE.Cost.Data.size_ofNat, MIPRE.Cost.Machine.Frame.toData, MIPRE.Cost.Machine.Cfg.toData, MIPRE.Cost.Machine.Ctrl.toData, MIPRE.Cost.Machine.evD, MIPRE.Cost.Machine.retD, MIPRE.Cost.Prog.toData, MIPRE.Cost.Data.list_cons, MIPRE.Cost.Data.list_nil, List.map_cons, List.map_nil] at *); all_goals omega)
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Prog
theorem retLoop1_runs_nil (b env' env k : Data) :
    ∃ s ≤ env'.size + k.size + 16,
      Eval [Data.cons .nil (.cons env (.cons (.cons b env') k))] retLoop1
        (.cons (retD .nil) (.cons env' k)) s := by
  have run : Eval [Data.cons .nil (.cons env (.cons (.cons b env') k))] retLoop1
      (.cons (retD .nil) (.cons env' k)) _ :=
    Eval.elim_cons (i := 0) (a := .nil) (b := .cons env (.cons (.cons b env') k)) (by simp)
      (Eval.elim_cons (i := 1) (a := env) (b := .cons (.cons b env') k) (by simp)
        (Eval.elim_cons (i := 1) (a := .cons b env') (b := k) (by simp)
          (Eval.elim_cons (i := 0) (a := b) (b := env') (by simp)
            (Eval.elim_nil (i := 6) (by simp)
              (Eval.cons (Eval.const _ (.cons (.cons .nil .nil) .nil))
                (Eval.cons (Eval.var_of_get (i := 1) (v := env') (by simp))
                  (Eval.var_of_get (i := 3) (v := k) (by simp))))))))
  refine ⟨_, ?_, run⟩
  ((try simp only [MIPRE.Cost.Data.size_cons, MIPRE.Cost.Data.size_nil, MIPRE.Cost.Data.size_ofNat, MIPRE.Cost.Machine.Frame.toData, MIPRE.Cost.Machine.Cfg.toData, MIPRE.Cost.Machine.Ctrl.toData, MIPRE.Cost.Machine.evD, MIPRE.Cost.Machine.retD, MIPRE.Cost.Prog.toData, MIPRE.Cost.Data.list_cons, MIPRE.Cost.Data.list_nil, List.map_cons, List.map_nil] at *); all_goals omega)
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Prog
theorem retLoop1_runs_stop (b env' c env k : Data) :
    ∃ s ≤ c.size + env'.size + k.size + 18,
      Eval [Data.cons (.cons .nil c) (.cons env (.cons (.cons b env') k))] retLoop1
        (.cons (retD c) (.cons env' k)) s := by
  have run : Eval [Data.cons (.cons .nil c) (.cons env (.cons (.cons b env') k))] retLoop1
      (.cons (retD c) (.cons env' k)) _ :=
    Eval.elim_cons (i := 0) (a := .cons .nil c) (b := .cons env (.cons (.cons b env') k))
      (by simp)
      (Eval.elim_cons (i := 1) (a := env) (b := .cons (.cons b env') k) (by simp)
        (Eval.elim_cons (i := 1) (a := .cons b env') (b := k) (by simp)
          (Eval.elim_cons (i := 0) (a := b) (b := env') (by simp)
            (Eval.elim_cons (i := 6) (a := .nil) (b := c) (by simp)
              (Eval.elim_nil (i := 0) (by simp)
                (Eval.cons (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _))
                    (Eval.var_of_get (i := 1) (v := c) (by simp)))
                  (Eval.cons (Eval.var_of_get (i := 3) (v := env') (by simp))
                    (Eval.var_of_get (i := 5) (v := k) (by simp)))))))))
  refine ⟨_, ?_, run⟩
  ((try simp only [MIPRE.Cost.Data.size_cons, MIPRE.Cost.Data.size_nil, MIPRE.Cost.Data.size_ofNat, MIPRE.Cost.Machine.Frame.toData, MIPRE.Cost.Machine.Cfg.toData, MIPRE.Cost.Machine.Ctrl.toData, MIPRE.Cost.Machine.evD, MIPRE.Cost.Machine.retD, MIPRE.Cost.Prog.toData, MIPRE.Cost.Data.list_cons, MIPRE.Cost.Data.list_nil, List.map_cons, List.map_nil] at *); all_goals omega)
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Prog
theorem retLoop1_runs_step (b env' a₁ a₂ c env k : Data) :
    ∃ s ≤ 2 * b.size + 2 * c.size + 2 * env'.size + k.size + 40,
      Eval [Data.cons (.cons (.cons a₁ a₂) c) (.cons env (.cons (.cons b env') k))] retLoop1
        (.cons (evD b) (.cons (.cons c env'.right)
          (.cons (.cons (.ofNat 3) (.cons b (.cons c env'.right))) k))) s := by
  obtain ⟨s₁, hs₁, hr₁⟩ := projRight_runs (E := a₁ :: a₂ :: Data.cons a₁ a₂ :: c :: b :: env' ::
    Data.cons b env' :: k :: env :: Data.cons (.cons b env') k :: Data.cons (.cons a₁ a₂) c ::
    Data.cons env (.cons (.cons b env') k) ::
    [Data.cons (.cons (.cons a₁ a₂) c) (.cons env (.cons (.cons b env') k))]) (i := 5) (d := env')
    (by simp)
  have run : Eval [Data.cons (.cons (.cons a₁ a₂) c) (.cons env (.cons (.cons b env') k))] retLoop1
      (.cons (evD b) (.cons (.cons c env'.right)
        (.cons (.cons (.ofNat 3) (.cons b (.cons c env'.right))) k))) _ :=
    Eval.elim_cons (i := 0) (a := .cons (.cons a₁ a₂) c) (b := .cons env (.cons (.cons b env') k))
      (by simp)
      (Eval.elim_cons (i := 1) (a := env) (b := .cons (.cons b env') k) (by simp)
        (Eval.elim_cons (i := 1) (a := .cons b env') (b := k) (by simp)
          (Eval.elim_cons (i := 0) (a := b) (b := env') (by simp)
            (Eval.elim_cons (i := 6) (a := .cons a₁ a₂) (b := c) (by simp)
              (Eval.elim_cons (i := 0) (a := a₁) (b := a₂) (by simp)
                (Eval.cons (Eval.cons (Eval.nil _) (Eval.var_of_get (i := 4) (v := b) (by simp)))
                  (Eval.cons (Eval.cons (Eval.var_of_get (i := 3) (v := c) (by simp)) hr₁)
                    (Eval.cons (Eval.cons (Eval.const _ (.ofNat 3))
                        (Eval.cons (Eval.var_of_get (i := 4) (v := b) (by simp))
                          (Eval.cons (Eval.var_of_get (i := 3) (v := c) (by simp)) hr₁)))
                      (Eval.var_of_get (i := 7) (v := k) (by simp))))))))))
  refine ⟨_, ?_, run⟩
  ((try simp only [MIPRE.Cost.Data.size_cons, MIPRE.Cost.Data.size_nil, MIPRE.Cost.Data.size_ofNat, MIPRE.Cost.Machine.Frame.toData, MIPRE.Cost.Machine.Cfg.toData, MIPRE.Cost.Machine.Ctrl.toData, MIPRE.Cost.Machine.evD, MIPRE.Cost.Machine.retD, MIPRE.Cost.Prog.toData, MIPRE.Cost.Data.list_cons, MIPRE.Cost.Data.list_nil, List.map_cons, List.map_nil] at *); all_goals omega)
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
theorem stepRetProg_prefix (ftag : ℕ) (fb v env k r : Data) {s : ℕ}
    (hd : Eval (retDispEnv ftag fb v env k) (dispatch retCases 0 1) r s) :
    ∃ c ≤ s + v.size + env.size + fb.size + k.size + (Data.ofNat ftag).size + 16,
      Eval [Data.cons v (.cons env (.cons (.cons (.ofNat ftag) fb) k))] stepRetProg r c := by
  have run : Eval [Data.cons v (.cons env (.cons (.cons (.ofNat ftag) fb) k))] stepRetProg r _ :=
    Eval.elim_cons (i := 0) (a := v) (b := .cons env (.cons (.cons (.ofNat ftag) fb) k)) (by simp)
      (Eval.elim_cons (i := 1) (a := env) (b := .cons (.cons (.ofNat ftag) fb) k) (by simp)
        (Eval.elim_cons (i := 1) (a := .cons (.ofNat ftag) fb) (b := k) (by simp)
          (Eval.elim_cons (i := 0) (a := .ofNat ftag) (b := fb) (by simp)
            (Eval.let_ (Eval.cons (Eval.var_of_get (i := 6) (v := v) (by simp))
                (Eval.cons (Eval.var_of_get (i := 4) (v := env) (by simp))
                  (Eval.cons (Eval.var_of_get (i := 1) (v := fb) (by simp))
                    (Eval.var_of_get (i := 3) (v := k) (by simp)))))
              (Eval.let_ (Eval.var_of_get (i := 1) (v := .ofNat ftag) (by simp)) hd)))))
  exact ⟨_, by omega, run⟩
end MIPRE.Cost.Machine

/-! The uploaded declaration, hoisted to the top level as `solution`. -/
open MIPRE
open MIPRE.Cost
open MIPRE.Cost.Machine
open MIPRE.Cost.Prog
theorem solution (v env : Data) (f : Frame) (k : Data) :
    ∃ s ≤ stepRetBound (v.size + env.size + (Frame.toData f).size + k.size),
      stepRetProg.Runs (.cons v (.cons env (.cons (Frame.toData f) k)))
        (stepRet v env (.cons (Frame.toData f) k)) s := by
  cases f with
  | cons1 t' env' =>
    obtain ⟨c₀, hc₀, hcase⟩ := retCons1_runs t'.toData (Data.list env') v env k
    obtain ⟨s, hs, hd⟩ := dispatch_runs retCases 0 0 1
      (retDispEnv 0 (.cons t'.toData (.list env')) v env k)
      (Data.cons v (.cons env (.cons (.cons t'.toData (.list env')) k))) _ c₀ (by simp [retCases])
      retCases_wellScoped (by simp [retDispEnv]) (by simp [retDispEnv])
      (show Eval [Data.cons v (.cons env (.cons (.cons t'.toData (.list env')) k))]
        (retCases.getD 0 .nil) _ _ from hcase)
    obtain ⟨c', hc', run⟩ := stepRetProg_prefix 0 (.cons t'.toData (.list env')) v env k _ hd
    refine ⟨_, ?_, by simpa [Prog.Runs, stepRet, Frame.toData] using run⟩
    unfold stepRetBound
    ((try simp only [MIPRE.Cost.Data.size_cons, MIPRE.Cost.Data.size_nil, MIPRE.Cost.Data.size_ofNat, MIPRE.Cost.Machine.Frame.toData, MIPRE.Cost.Machine.Cfg.toData, MIPRE.Cost.Machine.Ctrl.toData, MIPRE.Cost.Machine.evD, MIPRE.Cost.Machine.retD, MIPRE.Cost.Prog.toData, MIPRE.Cost.Data.list_cons, MIPRE.Cost.Data.list_nil, List.map_cons, List.map_nil] at *); all_goals omega)
  | cons2 a =>
    obtain ⟨c₀, hc₀, hcase⟩ := retCons2_runs a v env k
    obtain ⟨s, hs, hd⟩ := dispatch_runs retCases 1 0 1 (retDispEnv 1 a v env k)
      (Data.cons v (.cons env (.cons a k))) _ c₀ (by simp [retCases])
      retCases_wellScoped (by simp [retDispEnv]) (by simp [retDispEnv])
      (show Eval [Data.cons v (.cons env (.cons a k))] (retCases.getD 1 .nil) _ _ from hcase)
    obtain ⟨c', hc', run⟩ := stepRetProg_prefix 1 a v env k _ hd
    refine ⟨_, ?_, by simpa [Prog.Runs, stepRet, Frame.toData] using run⟩
    unfold stepRetBound
    ((try simp only [MIPRE.Cost.Data.size_cons, MIPRE.Cost.Data.size_nil, MIPRE.Cost.Data.size_ofNat, MIPRE.Cost.Machine.Frame.toData, MIPRE.Cost.Machine.Cfg.toData, MIPRE.Cost.Machine.Ctrl.toData, MIPRE.Cost.Machine.evD, MIPRE.Cost.Machine.retD, MIPRE.Cost.Prog.toData, MIPRE.Cost.Data.list_cons, MIPRE.Cost.Data.list_nil, List.map_cons, List.map_nil] at *); all_goals omega)
  | let1 b env' =>
    obtain ⟨c₀, hc₀, hcase⟩ := retLet1_runs b.toData (Data.list env') v env k
    obtain ⟨s, hs, hd⟩ := dispatch_runs retCases 2 0 1
      (retDispEnv 2 (.cons b.toData (.list env')) v env k)
      (Data.cons v (.cons env (.cons (.cons b.toData (.list env')) k))) _ c₀ (by simp [retCases])
      retCases_wellScoped (by simp [retDispEnv]) (by simp [retDispEnv])
      (show Eval [Data.cons v (.cons env (.cons (.cons b.toData (.list env')) k))]
        (retCases.getD 2 .nil) _ _ from hcase)
    obtain ⟨c', hc', run⟩ := stepRetProg_prefix 2 (.cons b.toData (.list env')) v env k _ hd
    refine ⟨_, ?_, by simpa [Prog.Runs, stepRet, Frame.toData] using run⟩
    unfold stepRetBound
    ((try simp only [MIPRE.Cost.Data.size_cons, MIPRE.Cost.Data.size_nil, MIPRE.Cost.Data.size_ofNat, MIPRE.Cost.Machine.Frame.toData, MIPRE.Cost.Machine.Cfg.toData, MIPRE.Cost.Machine.Ctrl.toData, MIPRE.Cost.Machine.evD, MIPRE.Cost.Machine.retD, MIPRE.Cost.Prog.toData, MIPRE.Cost.Data.list_cons, MIPRE.Cost.Data.list_nil, List.map_cons, List.map_nil] at *); all_goals omega)
  | loop1 b env' =>
    rcases v with _ | ⟨_ | ⟨a₁, a₂⟩, c⟩
    · obtain ⟨c₀, hc₀, hcase⟩ := retLoop1_runs_nil b.toData (Data.list env') env k
      obtain ⟨s, hs, hd⟩ := dispatch_runs retCases 3 0 1
        (retDispEnv 3 (.cons b.toData (.list env')) .nil env k)
        (Data.cons .nil (.cons env (.cons (.cons b.toData (.list env')) k))) _ c₀ (by simp [retCases])
        retCases_wellScoped (by simp [retDispEnv]) (by simp [retDispEnv])
        (show Eval [Data.cons .nil (.cons env (.cons (.cons b.toData (.list env')) k))]
          (retCases.getD 3 .nil) _ _ from hcase)
      obtain ⟨c', hc', run⟩ := stepRetProg_prefix 3 (.cons b.toData (.list env')) .nil env k _ hd
      refine ⟨_, ?_, by simpa [Prog.Runs, stepRet, Frame.toData] using run⟩
      unfold stepRetBound
      ((try simp only [MIPRE.Cost.Data.size_cons, MIPRE.Cost.Data.size_nil, MIPRE.Cost.Data.size_ofNat, MIPRE.Cost.Machine.Frame.toData, MIPRE.Cost.Machine.Cfg.toData, MIPRE.Cost.Machine.Ctrl.toData, MIPRE.Cost.Machine.evD, MIPRE.Cost.Machine.retD, MIPRE.Cost.Prog.toData, MIPRE.Cost.Data.list_cons, MIPRE.Cost.Data.list_nil, List.map_cons, List.map_nil] at *); all_goals omega)
    · obtain ⟨c₀, hc₀, hcase⟩ := retLoop1_runs_stop b.toData (Data.list env') c env k
      obtain ⟨s, hs, hd⟩ := dispatch_runs retCases 3 0 1
        (retDispEnv 3 (.cons b.toData (.list env')) (.cons .nil c) env k)
        (Data.cons (.cons .nil c) (.cons env (.cons (.cons b.toData (.list env')) k))) _ c₀
        (by simp [retCases]) retCases_wellScoped (by simp [retDispEnv]) (by simp [retDispEnv])
        (show Eval [Data.cons (.cons .nil c) (.cons env (.cons (.cons b.toData (.list env')) k))]
          (retCases.getD 3 .nil) _ _ from hcase)
      obtain ⟨c', hc', run⟩ :=
        stepRetProg_prefix 3 (.cons b.toData (.list env')) (.cons .nil c) env k _ hd
      refine ⟨_, ?_, by simpa [Prog.Runs, stepRet, Frame.toData] using run⟩
      unfold stepRetBound
      ((try simp only [MIPRE.Cost.Data.size_cons, MIPRE.Cost.Data.size_nil, MIPRE.Cost.Data.size_ofNat, MIPRE.Cost.Machine.Frame.toData, MIPRE.Cost.Machine.Cfg.toData, MIPRE.Cost.Machine.Ctrl.toData, MIPRE.Cost.Machine.evD, MIPRE.Cost.Machine.retD, MIPRE.Cost.Prog.toData, MIPRE.Cost.Data.list_cons, MIPRE.Cost.Data.list_nil, List.map_cons, List.map_nil] at *); all_goals omega)
    · obtain ⟨c₀, hc₀, hcase⟩ := retLoop1_runs_step b.toData (Data.list env') a₁ a₂ c env k
      obtain ⟨s, hs, hd⟩ := dispatch_runs retCases 3 0 1
        (retDispEnv 3 (.cons b.toData (.list env')) (.cons (.cons a₁ a₂) c) env k)
        (Data.cons (.cons (.cons a₁ a₂) c) (.cons env (.cons (.cons b.toData (.list env')) k))) _ c₀
        (by simp [retCases]) retCases_wellScoped (by simp [retDispEnv]) (by simp [retDispEnv])
        (show Eval [Data.cons (.cons (.cons a₁ a₂) c)
          (.cons env (.cons (.cons b.toData (.list env')) k))] (retCases.getD 3 .nil) _ _ from hcase)
      obtain ⟨c', hc', run⟩ :=
        stepRetProg_prefix 3 (.cons b.toData (.list env')) (.cons (.cons a₁ a₂) c) env k _ hd
      refine ⟨_, ?_, by simpa [Prog.Runs, stepRet, Frame.toData] using run⟩
      have hsz := size_right_le (Data.list env')
      unfold stepRetBound
      ((try simp only [MIPRE.Cost.Data.size_cons, MIPRE.Cost.Data.size_nil, MIPRE.Cost.Data.size_ofNat, MIPRE.Cost.Machine.Frame.toData, MIPRE.Cost.Machine.Cfg.toData, MIPRE.Cost.Machine.Ctrl.toData, MIPRE.Cost.Machine.evD, MIPRE.Cost.Machine.retD, MIPRE.Cost.Prog.toData, MIPRE.Cost.Data.list_cons, MIPRE.Cost.Data.list_nil, List.map_cons, List.map_nil] at *); all_goals omega)
