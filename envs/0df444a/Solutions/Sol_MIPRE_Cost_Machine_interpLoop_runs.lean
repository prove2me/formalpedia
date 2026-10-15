-- Prove2me | solution 1 for MIPRE.Cost.Machine.interpLoop_runs
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-12T16:45:10.700461+00:00
-- url     : https://prove2.me/submissions/b8a6d4f3-7814-4b4d-9910-e51026ba6f2d

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/Universal.lean (solution of MIPRE.Cost.Machine.interpLoop_runs);
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
import Theorems.Thm_MIPRE_Cost_Machine_stepProg_runs

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
theorem step_final (r : Data) (e : Env) (n : ℕ) :
    step^[n] (⟨.ret r, e, []⟩ : Cfg) = ⟨.ret r, e, []⟩ :=
  Function.iterate_fixed rfl n
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
theorem interpBodyBound_mono {S T : ℕ} (h : S ≤ T) : interpBodyBound S ≤ interpBodyBound T := by
  unfold interpBodyBound; have := stepBound_mono h; omega
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Polynomial
open Prog
theorem interpBody_final (r : Data) (e env : Env) :
    ∃ t ≤ 3 * (Cfg.toData ⟨.ret r, e, []⟩).size + 30,
      Eval (Cfg.toData ⟨.ret r, e, []⟩ :: env) interpBody (.cons .nil r) t := by
  obtain ⟨t₁, ht₁, h₁⟩ := isFinalProg_final r e
  have run : Eval (Cfg.toData ⟨.ret r, e, []⟩ :: env) interpBody (.cons .nil r) _ :=
    Eval.let_ (callVar_eval (i := 0) isFinalProg_wellScoped (v := Cfg.toData ⟨.ret r, e, []⟩)
        (by simp) h₁)
      (Eval.elim_cons (i := 0) (a := .nil) (b := r) (by simp)
        (Eval.cons (Eval.nil _) (Eval.var_of_get (i := 1) (v := r) (by simp))))
  refine ⟨_, ?_, run⟩
  have : r.size ≤ (Cfg.toData ⟨.ret r, e, []⟩).size := by
    simp only [Cfg.toData, Ctrl.toData, retD, Data.size_cons]; omega
  omega
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Polynomial
open Prog
theorem interpBody_step (c : Cfg) (h : ¬ IsFinal c) (env : Env) :
    ∃ t ≤ interpBodyBound (Cfg.toData c).size,
      Eval (c.toData :: env) interpBody (.cons (.cons .nil .nil) (step c).toData) t := by
  obtain ⟨t₁, ht₁, h₁⟩ := isFinalProg_nonfinal c h
  obtain ⟨t₂, ht₂, h₂⟩ := stepProg_runs c
  have run : Eval (c.toData :: env) interpBody (.cons (.cons .nil .nil) (step c).toData) _ :=
    Eval.let_ (callVar_eval (i := 0) isFinalProg_wellScoped (v := c.toData) (by simp) h₁)
      (Eval.elim_nil (i := 0) (by simp)
        (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _))
          (callVar_eval (i := 1) stepProg_wellScoped (v := c.toData) (by simp) h₂)))
  refine ⟨_, ?_, run⟩
  unfold interpBodyBound
  omega
end MIPRE.Cost.Machine

/-! The uploaded declaration, hoisted to the top level as `solution`. -/
open MIPRE
open MIPRE.Cost
open MIPRE.Cost.Machine
open Polynomial
open MIPRE.Cost.Prog
theorem solution (c₀ : Cfg) (S : ℕ) (hS : ∀ n, (step^[n] c₀).toData.size ≤ S)
    (r : Data) (e : Env) (N : ℕ) (hN : step^[N] c₀ = ⟨.ret r, e, []⟩) (env : Env) :
    ∀ m n, n + m = N → ∃ t ≤ (m + 1) * (interpBodyBound S + 1),
      Eval ((step^[n] c₀).toData :: env) (.loop interpBody) r t := by
  intro m
  induction m with
  | zero =>
    intro n hn
    have hn' : step^[n] c₀ = ⟨.ret r, e, []⟩ := by rw [← hN, ← hn, Nat.add_zero]
    rw [hn']
    obtain ⟨t, ht, hb⟩ := interpBody_final r e env
    refine ⟨t + 1, ?_, Eval.loop_stop hb⟩
    have h1 := hS n
    rw [hn'] at h1
    have h2 := Nat.le_mul_of_pos_left (interpBodyBound S + 1) (show 0 < 0 + 1 by omega)
    unfold interpBodyBound at h2 ⊢
    omega
  | succ m ih =>
    intro n hn
    by_cases hf : IsFinal (step^[n] c₀)
    · obtain ⟨r', e', hr'⟩ := hf
      have hN' : (⟨.ret r, e, []⟩ : Cfg) = ⟨.ret r', e', []⟩ := by
        rw [← hN, show N = (m + 1) + n by omega, Function.iterate_add_apply, hr', step_final]
      obtain ⟨rfl, rfl⟩ : r = r' ∧ e = e' := by simpa using hN'
      rw [hr']
      obtain ⟨t, ht, hb⟩ := interpBody_final r e env
      refine ⟨t + 1, ?_, Eval.loop_stop hb⟩
      have h1 := hS n
      rw [hr'] at h1
      have h2 := Nat.le_mul_of_pos_left (interpBodyBound S + 1) (show 0 < m + 1 + 1 by omega)
      unfold interpBodyBound at h2 ⊢
      omega
    · obtain ⟨t₁, ht₁, hb⟩ := interpBody_step (step^[n] c₀) hf env
      obtain ⟨t₂, ht₂, hrest⟩ := ih (n + 1) (by omega)
      rw [Function.iterate_succ_apply'] at hrest
      refine ⟨t₁ + t₂ + 1, ?_, Eval.loop_step hb hrest⟩
      have hmono := interpBodyBound_mono (hS n)
      rw [Nat.succ_mul]
      omega
