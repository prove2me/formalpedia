-- Prove2me | solution 1 for MIPRE.Cost.Prog.repDecCore_runs_malformed
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-16T15:34:10.414689+00:00
-- url     : https://prove2.me/submissions/df85225d-0a1e-46c1-a22d-995ce89ba127

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Repeat/DecMain.lean (solution of MIPRE.Cost.Prog.repDecCore_runs_malformed);
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

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Cost.Prog
open Data
theorem _root_.solution (univ : Prog) (sP dP lamD tauD betaD nD d : Data)
    (hd : d = .nil ∨ (∃ xD, d = .cons xD .nil) ∨ ∃ xD yD, d = .cons xD (.cons yD .nil)) :
    ∃ t ≤ 10, Eval [Data.cons (decParams sP dP lamD tauD betaD) (.cons nD d)] (repDecCore univ) .nil t := by
  have pre : ∀ {c : Prog} {r : Data} {t : ℕ},
      Eval [nD, d, tauD, betaD, lamD, .cons tauD betaD, sP, dP, .cons sP dP,
        .cons lamD (.cons tauD betaD), decParams sP dP lamD tauD betaD, .cons nD d,
        .cons (decParams sP dP lamD tauD betaD) (.cons nD d)] c r t →
      Eval [Data.cons (decParams sP dP lamD tauD betaD) (.cons nD d)]
        (.elim 0 .nil (.elim 0 .nil (.elim 0 .nil (.elim 3 .nil (.elim 1 .nil (.elim 9 .nil c)))))) r
        (t + 6) := fun hc =>
    Eval.elim_cons (i := 0) (n := .nil) (a := decParams sP dP lamD tauD betaD) (b := .cons nD d) (by simp)
      (Eval.elim_cons (i := 0) (n := .nil) (a := .cons sP dP) (b := .cons lamD (.cons tauD betaD))
        (by simp [decParams])
        (Eval.elim_cons (i := 0) (n := .nil) (a := sP) (b := dP) (by simp)
          (Eval.elim_cons (i := 3) (n := .nil) (a := lamD) (b := .cons tauD betaD) (by simp)
            (Eval.elim_cons (i := 1) (n := .nil) (a := tauD) (b := betaD) (by simp)
              (Eval.elim_cons (i := 9) (n := .nil) (a := nD) (b := d) (by simp) hc)))))
  rcases hd with rfl | ⟨xD, rfl⟩ | ⟨xD, yD, rfl⟩
  · exact ⟨_, by omega, pre (Eval.elim_nil (i := 1) (by simp) (Eval.nil _))⟩
  · exact ⟨_, by omega, pre (Eval.elim_cons (i := 1) (n := .nil) (a := xD) (b := .nil) (by simp)
      (Eval.elim_nil (i := 1) (by simp) (Eval.nil _)))⟩
  · exact ⟨_, by omega, pre (Eval.elim_cons (i := 1) (n := .nil) (a := xD) (b := .cons yD .nil) (by simp)
      (Eval.elim_cons (i := 1) (n := .nil) (a := yD) (b := .nil) (by simp)
        (Eval.elim_nil (i := 1) (by simp) (Eval.nil _))))⟩
end MIPRE.Cost.Prog
