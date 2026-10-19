-- Prove2me | solution 1 for MIPRE.Cost.Prog.repDecCore_inv
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-16T15:34:01.656386+00:00
-- url     : https://prove2.me/submissions/4e2d5667-fc0c-4e83-99f6-0640105eb36a

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Repeat/DecMain.lean (solution of MIPRE.Cost.Prog.repDecCore_inv);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Computability.Primrec.List
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Halting_Descriptions
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Halting_Lists
import Definitions.Def_MIPRE_Foundations_Halting_Lists_B
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Foundations_Halting_Arith
import Definitions.Def_MIPRE_Foundations_Repeat_Prims
import Definitions.Def_MIPRE_Foundations_Repeat_MapLoop
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit_B
import Definitions.Def_MIPRE_Foundations_Repeat_Sampler
import Definitions.Def_MIPRE_Foundations_CL_Repeat
import Definitions.Def_MIPRE_Foundations_Repeat_Bits
import Definitions.Def_MIPRE_Foundations_Cost_Machine_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineData_B
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound_B
import Definitions.Def_MIPRE_Foundations_Cost_Universal_B
import Definitions.Def_MIPRE_Foundations_Cost_Kleene_B
import Definitions.Def_MIPRE_Foundations_Repeat_DecLoop
import Definitions.Def_MIPRE_Foundations_Halting_Serial
import Definitions.Def_MIPRE_Foundations_Repeat_DecMain
import Theorems.Thm_MIPRE_Cost_Eval_deterministic

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.Cost.Prog
section
open Data
theorem bitWalkBody_wellScoped : bitWalkBody.WellScoped 1 := by
  simp [bitWalkBody, WellScoped]
end
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
section
open Data
theorem bitWalkProg_wellScoped : bitWalkProg.WellScoped 1 :=
  ⟨Nat.zero_lt_one, bitWalkBody_wellScoped⟩
end
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
section
open Data
theorem powBody_wellScoped : powBody.WellScoped 1 := by
  simp [powBody, WellScoped, lenBody]
end
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
section
open Data
theorem dblBody_wellScoped : dblBody.WellScoped 1 := by
  simp [dblBody, WellScoped, revOntoProg, revOntoBody]
end
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
section
open Data
theorem pairTakeProg_wellScoped : pairTakeProg.WellScoped 1 := by
  simp [pairTakeProg, WellScoped, takeBody, callVar, revProg, revOntoProg, revOntoBody]
end
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
section
open Data
theorem finalProg_wellScoped : finalProg.WellScoped 1 := by simp [finalProg, WellScoped]
end
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
section
open Data
theorem preProg_wellScoped : preProg.WellScoped 1 := by
  simp only [preProg, WellScoped, callVar]
  refine ⟨by omega, trivial, by omega, trivial, by omega, trivial, by omega, trivial, by omega,
    trivial, by omega, trivial, by omega, trivial, by omega, trivial, by omega, trivial, by omega,
    trivial, ⟨by omega, by omega, by omega⟩, ⟨by omega, pairTakeProg_wellScoped.mono (by omega) _⟩,
    ⟨by omega, by omega⟩, ⟨by omega, bitWalkProg_wellScoped.mono (by omega) _⟩, by omega, trivial,
    by omega, ⟨⟨by omega, by omega⟩, ⟨by omega, bitWalkProg_wellScoped.mono (by omega) _⟩, by omega,
      trivial, by omega, ⟨by omega, trivial, by omega, trivial, by omega, trivial,
        ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩,
        ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩⟩, trivial⟩, trivial⟩
end
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
section
open Data
theorem stepProg_wellScoped {univ : Prog} (hU : univ.WellScoped 1) :
    (stepProg univ).WellScoped 1 := by
  simp only [stepProg, WellScoped, callVar]
  exact ⟨⟨by omega, preProg_wellScoped.mono (by omega) _⟩, by omega, ⟨trivial, trivial⟩,
    ⟨by omega, hU.mono (by omega) _⟩, by omega, ⟨trivial, trivial⟩, by omega, ⟨by omega,
      ⟨⟨trivial, trivial⟩, by omega⟩, ⟨trivial, trivial⟩⟩, ⟨trivial, trivial⟩⟩
end
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
section
open Data
theorem coordBody_wellScoped {univ : Prog} (hU : univ.WellScoped 1) :
    (coordBody univ).WellScoped 1 := by
  simp only [coordBody, WellScoped, callVar]
  exact ⟨by omega, trivial, by omega, ⟨by omega, finalProg_wellScoped.mono (by omega) _⟩,
    ⟨by omega, by omega⟩, by omega, (stepProg_wellScoped hU).mono (by omega) _⟩
end
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
section
open Data
theorem parseProg_wellScoped : parseProg.WellScoped 1 := by simp [parseProg, WellScoped, parseBody]
end
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
section
open Data
theorem bitsProg_wellScoped : bitsProg.WellScoped 1 := by
  simp [bitsProg, WellScoped, bitsBody, callVar, revProg, revOntoProg, revOntoBody]
end
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
section
open Data
theorem powLoop_wellScoped : (Prog.loop powBody).WellScoped 1 := ⟨Nat.zero_lt_one, powBody_wellScoped⟩
end
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
section
open Data
theorem dblLoop_wellScoped : (Prog.loop dblBody).WellScoped 1 := ⟨Nat.zero_lt_one, dblBody_wellScoped⟩
end
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
section
open Data
theorem prepProg_wellScoped {univ : Prog} (hU : univ.WellScoped 1) : (prepProg univ).WellScoped 1 := by
  simp only [prepProg, WellScoped, callVar, andExpr]
  repeat' first
    | exact hU.mono (by omega) _
    | exact toUnaryProg_wellScoped.mono (by omega) _
    | exact powLoop_wellScoped.mono (by omega) _
    | exact dblLoop_wellScoped.mono (by omega) _
    | exact bitsProg_wellScoped.mono (by omega) _
    | exact lenProg_wellScoped.mono (by omega) _
    | exact eqBitsProg_wellScoped.mono (by omega) _
    | exact parseProg_wellScoped.mono (by omega) _
    | exact serProg_wellScoped.mono (by omega) _
    | constructor
    | trivial
    | omega
end
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
section
open Data
theorem coordLoop_wellScoped {univ : Prog} (hU : univ.WellScoped 1) :
    (Prog.loop (coordBody univ)).WellScoped 1 := ⟨Nat.zero_lt_one, coordBody_wellScoped hU⟩
end
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
section
open Data
theorem decMain_wellScoped {univ : Prog} (hU : univ.WellScoped 1) : (decMain univ).WellScoped 1 :=
  ⟨prepProg_wellScoped hU, by omega, trivial,
    callVar_wellScoped (by omega) (coordLoop_wellScoped hU)⟩
end
end MIPRE.Cost.Prog

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Cost.Prog
open Data
theorem _root_.solution {univ : Prog} (hU : univ.WellScoped 1) (sP dP lamD tauD betaD nD xD yD aD bD : Data)
    {r : Data} {t : ℕ}
    (h : Eval [Data.cons (decParams sP dP lamD tauD betaD) (.cons nD (.cons xD (.cons yD (.cons aD bD))))]
      (repDecCore univ) r t) :
    ∃ t', Eval [decInput sP dP lamD tauD betaD nD xD yD aD bD] (decMain univ) r t' := by
  change Eval _ (.elim 0 .nil _) r t at h
  cases h with
  | elim_nil hn _ => simp at hn
  | elim_cons hc h1 =>
    simp only [Env.get_cons_zero, Data.cons.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    cases h1 with
    | elim_nil hn _ => simp [decParams] at hn
    | elim_cons hc h2 =>
      simp only [Env.get_cons_zero, decParams, Data.cons.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      cases h2 with
      | elim_nil hn _ => simp at hn
      | elim_cons hc h3 =>
        simp only [Env.get_cons_zero, Data.cons.injEq] at hc
        obtain ⟨rfl, rfl⟩ := hc
        cases h3 with
        | elim_nil hn _ => simp at hn
        | elim_cons hc h4 =>
          simp only [Env.get_cons_succ, Env.get_cons_zero, Data.cons.injEq] at hc
          obtain ⟨rfl, rfl⟩ := hc
          cases h4 with
          | elim_nil hn _ => simp at hn
          | elim_cons hc h5 =>
            simp only [Env.get_cons_succ, Env.get_cons_zero, Data.cons.injEq] at hc
            obtain ⟨rfl, rfl⟩ := hc
            cases h5 with
            | elim_nil hn _ => simp at hn
            | elim_cons hc h6 =>
              simp only [Env.get_cons_succ, Env.get_cons_zero, Data.cons.injEq] at hc
              obtain ⟨rfl, rfl⟩ := hc
              cases h6 with
              | elim_nil hn _ => simp at hn
              | elim_cons hc h7 =>
                simp only [Env.get_cons_succ, Env.get_cons_zero, Data.cons.injEq] at hc
                obtain ⟨rfl, rfl⟩ := hc
                cases h7 with
                | elim_nil hn _ => simp at hn
                | elim_cons hc h8 =>
                  simp only [Env.get_cons_succ, Env.get_cons_zero, Data.cons.injEq] at hc
                  obtain ⟨rfl, rfl⟩ := hc
                  cases h8 with
                  | elim_nil hn _ => simp at hn
                  | elim_cons hc h9 =>
                    simp only [Env.get_cons_succ, Env.get_cons_zero, Data.cons.injEq] at hc
                    obtain ⟨rfl, rfl⟩ := hc
                    cases h9 with
                    | let_ hA hB =>
                      obtain ⟨rfl, -⟩ := hA.deterministic (Eval.cons (Eval.var_of_get (i := 12) (v := sP) (by simp))
                        (Eval.cons (Eval.var_of_get (i := 13) (v := dP) (by simp))
                          (Eval.cons (Eval.var_of_get (i := 10) (v := lamD) (by simp))
                            (Eval.cons (Eval.var_of_get (i := 8) (v := tauD) (by simp))
                              (Eval.cons (Eval.var_of_get (i := 9) (v := betaD) (by simp))
                                (Eval.cons (Eval.var_of_get (i := 6) (v := nD) (by simp))
                                  (Eval.cons (Eval.var_of_get (i := 4) (v := xD) (by simp))
                                    (Eval.cons (Eval.var_of_get (i := 2) (v := yD) (by simp))
                                      (Eval.cons (Eval.var_of_get (i := 0) (v := aD) (by simp))
                                        (Eval.var_of_get (i := 1) (v := bD) (by simp)))))))))))
                      obtain ⟨t', -, h'⟩ := callVar_runs_rev (decMain_wellScoped hU) hB
                      simp only [Env.get_cons_zero] at h'
                      exact ⟨t', h'⟩
end MIPRE.Cost.Prog
