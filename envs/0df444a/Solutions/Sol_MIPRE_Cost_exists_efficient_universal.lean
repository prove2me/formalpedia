-- Prove2me | solution 1 for MIPRE.Cost.exists_efficient_universal
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-12T16:46:32.021696+00:00
-- url     : https://prove2.me/submissions/072dedfe-d9f1-4c9b-94fc-671ab1bd32ed

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/Universal.lean (solution of MIPRE.Cost.exists_efficient_universal);
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
import Theorems.Thm_MIPRE_Cost_Eval_deterministic
import Theorems.Thm_MIPRE_Cost_Machine_eval_steps_bound
import Theorems.Thm_MIPRE_Cost_Machine_eval_steps_count
import Theorems.Thm_MIPRE_Cost_Machine_halts_iff
import Theorems.Thm_MIPRE_Cost_Machine_interpLoop_rev
import Theorems.Thm_MIPRE_Cost_Machine_interpLoop_runs
import Theorems.Thm_MIPRE_Cost_Machine_size_toData_le

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context; each is used only by proofs. -/
namespace MIPRE.Cost
theorem esize_pos {α : Type*} [SizedEncoding α] (a : α) : 0 < esize a := Data.size_pos _
end MIPRE.Cost

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
theorem FrameBound.mono {V L P V' L' P' : ℕ} (hV : V ≤ V') (hL : L ≤ L') (hP : P ≤ P')
    {f : Frame} (h : FrameBound V L P f) : FrameBound V' L' P' f := by
  cases f with
  | cons2 a => exact le_trans h hV
  | cons1 t env => exact ⟨le_trans h.1 hP, le_trans h.2.1 hL, fun v hv => le_trans (h.2.2 v hv) hV⟩
  | let1 b env => exact ⟨le_trans h.1 hP, le_trans h.2.1 hL, fun v hv => le_trans (h.2.2 v hv) hV⟩
  | loop1 b env => exact ⟨le_trans h.1 hP, le_trans h.2.1 hL, fun v hv => le_trans (h.2.2 v hv) hV⟩
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
theorem CfgBound.mono {V L P K V' L' P' K' : ℕ} (hV : V ≤ V') (hL : L ≤ L') (hP : P ≤ P')
    (hK : K ≤ K') {c : Cfg} (h : CfgBound V L P K c) : CfgBound V' L' P' K' c where
  ctrl_val v hv := le_trans (h.ctrl_val v hv) hV
  ctrl_prog p hp := le_trans (h.ctrl_prog p hp) hP
  env_len := le_trans h.env_len hL
  env_val v hv := le_trans (h.env_val v hv) hV
  kont_len := le_trans h.kont_len hK
  frames f hf := (h.frames f hf).mono hV hL hP
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
theorem step_final (r : Data) (e : Env) (n : ℕ) :
    step^[n] (⟨.ret r, e, []⟩ : Cfg) = ⟨.ret r, e, []⟩ :=
  Function.iterate_fixed rfl n
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
/-- Along the run of a derivation from the empty stack, every configuration — also after
the final one, which is fixed — is bounded. -/
theorem eval_steps_bound_forever {env : Env} {p : Prog} {r : Data} {t : ℕ} (h : Eval env p r t)
    (V L P K : ℕ) (hb : CfgBound V L P K ⟨.ev p, env, []⟩) (ht : t ≤ V) :
    ∃ N env', Steps ⟨.ev p, env, []⟩ N ⟨.ret r, env', []⟩ t ∧
      ∀ n, CfgBound V (L + 2 * t) P (K + t) (step^[n] ⟨.ev p, env, []⟩) := by
  obtain ⟨N, env', hs, hb'⟩ := eval_steps_bound h [] V L P K hb ht
  refine ⟨N, env', hs, fun n => ?_⟩
  by_cases hn : n ≤ N
  · exact hb' n hn
  · obtain ⟨m, rfl⟩ : ∃ m, n = N + m := ⟨n - N, by omega⟩
    have hN := hb' N le_rfl
    rw [show N + m = m + N by omega, Function.iterate_add_apply, hs.1, step_final]
    rwa [hs.1] at hN
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Polynomial
open Prog
theorem isFinalProg_wellScoped : isFinalProg.WellScoped 1 := by simp [isFinalProg, WellScoped]
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Polynomial
open Prog
theorem interpBody_wellScoped : interpBody.WellScoped 1 :=
  ⟨callVar_wellScoped (by decide) isFinalProg_wellScoped,
    ⟨by decide, ⟨⟨trivial, trivial⟩, callVar_wellScoped (by decide) stepProg_wellScoped⟩,
      ⟨trivial, by simp [WellScoped]⟩⟩⟩
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Polynomial
open Prog
theorem univPrelude_runs (c v : Data) :
    ∃ t ≤ c.size + v.size + 10, Eval [Data.cons c v] univPrelude (initData c v) t := by
  have run : Eval [Data.cons c v] univPrelude (initData c v) _ :=
    Eval.elim_cons (i := 0) (a := c) (b := v) (by simp)
      (Eval.cons (Eval.cons (Eval.nil _) (Eval.var_of_get (i := 0) (v := c) (by simp)))
        (Eval.cons (Eval.cons (Eval.var_of_get (i := 1) (v := v) (by simp)) (Eval.nil _))
          (Eval.nil _)))
  exact ⟨_, by omega, run⟩
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Polynomial
open Prog
theorem univProg_wellScoped : univProg.WellScoped 1 :=
  ⟨⟨by decide, trivial, ⟨⟨trivial, by simp [WellScoped]⟩,
      ⟨⟨by simp [WellScoped], trivial⟩, trivial⟩⟩⟩,
    ⟨by decide, interpBody_wellScoped.mono (by omega) _⟩⟩
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Polynomial
open Prog
theorem univProg_time_le (c : Prog) (v r : Data) (t : ℕ) (h : c.Runs v r t) :
    ∃ t' ≤ univBoundFun (esize c + v.size + t), univProg.Runs (.cons (encode c) v) r t' := by
  set X := esize c + v.size + t with hX
  have hb : CfgBound X X X X ⟨.ev c, [v], []⟩ :=
    ⟨fun _ hv => by simp at hv,
      fun p hp => by
        simp only [Ctrl.ev.injEq] at hp
        subst hp
        omega,
      by
        simp only [List.length_cons, List.length_nil]
        have := esize_pos c
        omega,
      fun w hw => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        subst hw
        omega,
      by simp,
      fun f hf => by simp at hf⟩
  obtain ⟨N, e, hs, hbound⟩ := eval_steps_bound_forever h X X X X hb (by omega)
  have hsize : ∀ n, (step^[n] ⟨.ev c, [v], []⟩).toData.size ≤ sigmaFun X := fun n =>
    size_toData_le ((hbound n).mono le_rfl (by omega) le_rfl (by omega))
  obtain ⟨N', e', hs', hN'⟩ := eval_steps_count h []
  obtain ⟨t₀, ht₀, h₀⟩ := univPrelude_runs c.toData v
  obtain ⟨t₁, ht₁, h₁⟩ := interpLoop_runs ⟨.ev c, [v], []⟩ (sigmaFun X) hsize r e' N' hs'.1
    [Data.cons c.toData v] N' 0 (by omega)
  rw [Function.iterate_zero_apply] at h₁
  refine ⟨t₀ + t₁ + 1, ?_, Eval.let_ h₀ h₁⟩
  have hP : esize c = c.toData.size := rfl
  have hmul := Nat.mul_le_mul_right (interpBodyBound (sigmaFun X) + 1)
    (show N' + 1 ≤ 3 * X + 1 by omega)
  unfold univBoundFun
  omega
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Polynomial
open Prog
theorem univProg_halts_of (c : Prog) (v r : Data) (t' : ℕ)
    (h : univProg.Runs (.cons (encode c) v) r t') : ∃ t, c.Runs v r t := by
  change Eval [Data.cons c.toData v] (.let_ univPrelude (.loop interpBody)) r t' at h
  cases h with
  | let_ h₀ h₁ =>
    obtain ⟨t₀, -, h₀'⟩ := univPrelude_runs c.toData v
    obtain ⟨rfl, -⟩ := Eval.deterministic h₀' h₀
    obtain ⟨N, e, hN⟩ := interpLoop_rev _ ⟨.ev c, [v], []⟩ _ r h₁
    exact (halts_iff c v r).2 ⟨N, e, hN⟩
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Polynomial
open Prog
theorem stepPoly_eval (x : ℕ) : stepPoly.eval x = stepBound x := by
  simp only [stepPoly, eval_add, eval_mul, eval_X, eval_C, stepBound]
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Polynomial
open Prog
theorem interpBodyPoly_eval (x : ℕ) : interpBodyPoly.eval x = interpBodyBound x := by
  simp only [interpBodyPoly, eval_add, eval_mul, eval_X, eval_C, stepPoly_eval, interpBodyBound]
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Polynomial
open Prog
theorem sigmaPoly_eval (x : ℕ) : sigmaPoly.eval x = sigmaFun x := by
  simp only [sigmaPoly, eval_add, eval_mul, eval_X, eval_C, sigmaFun, cfgSizeBound]
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Polynomial
open Prog
theorem univPoly_eval (x : ℕ) : univPoly.eval x = univBoundFun x := by
  simp only [univPoly, eval_add, eval_mul, eval_X, eval_C, eval_comp, interpBodyPoly_eval,
    sigmaPoly_eval, univBoundFun]
end MIPRE.Cost.Machine

namespace MIPRE.Cost
open Polynomial
/-- The universal machine given by the self-interpreter. -/
noncomputable def selfUniversal : UniversalMachine where
  univ := Machine.univProg
  closed := Machine.univProg_wellScoped
  bound := Machine.univPoly
  time_le c v r t h := by
    rw [Machine.univPoly_eval]
    exact Machine.univProg_time_le c v r t h
  halts_of := Machine.univProg_halts_of
end MIPRE.Cost

/-! The uploaded declaration, hoisted to the top level as `solution`. -/
open MIPRE
open MIPRE.Cost
open Polynomial
theorem solution : Nonempty UniversalMachine := ⟨selfUniversal⟩
