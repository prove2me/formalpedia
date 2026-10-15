-- Prove2me | solution 1 for MIPRE.Cost.exists_clocked_universal
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-12T17:01:36.421602+00:00
-- url     : https://prove2.me/submissions/051cf812-4e07-466e-b29e-35a610d76c74

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/Universal.lean (solution of MIPRE.Cost.exists_clocked_universal);
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
import Theorems.Thm_MIPRE_Cost_Machine_univTProg_runs

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
open Polynomial
open Prog
theorem isFinalProg_wellScoped : isFinalProg.WellScoped 1 := by simp [isFinalProg, WellScoped]
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
theorem tripleBody_wellScoped : tripleBody.WellScoped 1 := by simp [tripleBody, WellScoped]
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Polynomial
open Prog
theorem tripleProg_wellScoped : tripleProg.WellScoped 1 := ⟨Nat.zero_lt_one, tripleBody_wellScoped⟩
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Polynomial
open Prog
theorem repBody_wellScoped : repBody.WellScoped 1 := by simp [repBody, WellScoped]
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Polynomial
open Prog
theorem repProg_wellScoped : repProg.WellScoped 1 := ⟨Nat.zero_lt_one, repBody_wellScoped⟩
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

namespace MIPRE.Cost.Machine
open Polynomial
open Prog
theorem clockRest_wellScoped : clockRest.WellScoped 14 := by
  simp [clockRest, WellScoped, callVar_wellScoped (show 11 < 14 by decide) stepProg_wellScoped,
    callVar_wellScoped (show 0 < 15 by decide) sizeProg_wellScoped,
    callVar_wellScoped (show 0 < 16 by decide) subProg_wellScoped]
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Polynomial
open Prog
theorem clockStep_wellScoped : clockStep.WellScoped 8 := by
  simp [clockStep, WellScoped, callVar_wellScoped (show 7 < 10 by decide) stepCostProg_wellScoped,
    callVar_wellScoped (show 0 < 11 by decide) subProg_wellScoped, clockRest_wellScoped]
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Polynomial
open Prog
theorem clockBody_wellScoped : clockBody.WellScoped 1 := by
  simp [clockBody, WellScoped, callVar_wellScoped (show 4 < 7 by decide) isFinalProg_wellScoped,
    clockStep_wellScoped]
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Polynomial
open Prog
theorem univTProg_wellScoped : univTProg.WellScoped 1 := by
  simp [univTProg, WellScoped, callVar_wellScoped, sizeProg_wellScoped, addProg_wellScoped,
    tripleProg_wellScoped, repProg_wellScoped,
    Prog.WellScoped.mono (show 1 ≤ 24 by omega) clockBody clockBody_wellScoped]
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
theorem sizePoly_eval (p : Polynomial ℕ) (x : ℕ) : (sizePoly p).eval x = sizeBound (p.eval x) := by
  simp only [sizePoly, eval_add, eval_mul, eval_C, sizeBound]
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Polynomial
open Prog
theorem addPoly_eval (p q : Polynomial ℕ) (x : ℕ) :
    (addPoly p q).eval x = addBound (p.eval x) (q.eval x) := by
  simp only [addPoly, eval_add, eval_mul, eval_C, addBound]
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Polynomial
open Prog
theorem triplePoly_eval (p q : Polynomial ℕ) (x : ℕ) :
    (triplePoly p q).eval x = tripleBound (p.eval x) (q.eval x) := by
  simp only [triplePoly, eval_add, eval_mul, eval_C, tripleBound]
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Polynomial
open Prog
theorem repPoly_eval (p q r : Polynomial ℕ) (x : ℕ) :
    (repPoly p q r).eval x = repBound (p.eval x) (q.eval x) (r.eval x) := by
  simp only [repPoly, eval_add, eval_mul, eval_C, repBound]
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Polynomial
open Prog
theorem subPoly_eval (p q : Polynomial ℕ) (x : ℕ) :
    (subPoly p q).eval x = subBound (p.eval x) (q.eval x) := by
  simp only [subPoly, eval_add, eval_mul, eval_C, subBound]
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Polynomial
open Prog
theorem stepCostPoly_eval (p : Polynomial ℕ) (x : ℕ) :
    (stepCostPoly p).eval x = stepCostBound (p.eval x) := by
  simp only [stepCostPoly, eval_add, eval_mul, eval_C, stepCostBound]
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Polynomial
open Prog
theorem clockBodyPoly_eval (p q : Polynomial ℕ) (x : ℕ) :
    (clockBodyPoly p q).eval x = clockBodyBound (p.eval x) (q.eval x) := by
  simp only [clockBodyPoly, eval_add, eval_mul, eval_C, eval_comp, stepCostPoly_eval, subPoly_eval,
    stepPoly_eval, sizePoly_eval, clockBodyBound]
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Polynomial
open Prog
theorem guardPoly_eval (x : ℕ) : guardPoly.eval x = guardFun x := by
  simp only [guardPoly, eval_add, eval_mul, eval_C, eval_X, guardFun]
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Polynomial
open Prog
theorem t1Poly_eval (x : ℕ) : t1Poly.eval x = t1Fun x := by
  simp only [t1Poly, eval_add, eval_mul, eval_C, guardPoly_eval, t1Fun]
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Polynomial
open Prog
theorem thetaPoly_eval (x : ℕ) : thetaPoly.eval x = thetaFun x := by
  simp only [thetaPoly, eval_add, eval_mul, eval_C, guardPoly_eval, t1Poly_eval, thetaFun]
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Polynomial
open Prog
theorem univTPoly_eval (x : ℕ) : univTPoly.eval x = univTBoundFun x := by
  simp only [univTPoly, eval_add, eval_mul, eval_C, eval_X, sizePoly_eval, addPoly_eval,
    triplePoly_eval, repPoly_eval, clockBodyPoly_eval, guardPoly_eval, t1Poly_eval,
    thetaPoly_eval, univTBoundFun]
end MIPRE.Cost.Machine

namespace MIPRE.Cost
open Polynomial
/-- The clocked universal machine given by the self-interpreter. -/
noncomputable def selfClockedUniversal : ClockedUniversalMachine where
  univT := Machine.univTProg
  closed := Machine.univTProg_wellScoped
  bound := Machine.univTPoly
  run c v k := by
    rw [Machine.univTPoly_eval]
    exact Machine.univTProg_runs c v k
end MIPRE.Cost

/-! The uploaded declaration, hoisted to the top level as `solution`. -/
open MIPRE
open MIPRE.Cost
open Polynomial
theorem solution : Nonempty ClockedUniversalMachine := ⟨selfClockedUniversal⟩
