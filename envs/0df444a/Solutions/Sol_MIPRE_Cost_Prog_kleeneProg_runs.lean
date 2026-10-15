-- Prove2me | solution 1 for MIPRE.Cost.Prog.kleeneProg_runs
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-12T16:31:47.816806+00:00
-- url     : https://prove2.me/submissions/df7ca71d-a2f4-450e-afe3-21bb6c0bca7e

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/Kleene.lean (solution of MIPRE.Cost.Prog.kleeneProg_runs);
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
import Definitions.Def_MIPRE_Foundations_Cost_Kleene

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context; each is used only by proofs. -/
namespace MIPRE.Cost.Prog
open Polynomial
/-- The run of the pairing prefix of `kleeneProg`. -/
theorem kleeneProg_pair_eval (x : Prog) (v : Data) :
    Eval [encode x, v, Data.cons (encode x) v] (.cons (.var 0) (.var 0))
      (.cons (encode x) (encode x)) ((encode x).size + 1 + ((encode x).size + 1) + 1) :=
  Eval.cons (Eval.var_of_get (i := 0) (v := encode x) (by simp))
    (Eval.var_of_get (i := 0) (v := encode x) (by simp))
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
open Polynomial
/-- The run of the s-m-n step of `kleeneProg`. -/
theorem kleeneProg_smn_eval (x : Prog) (v : Data) :
    Eval [Data.cons (encode x) (encode x), encode x, v, Data.cons (encode x) v]
      (callVar 0 smnProg) (encode (hardcode x (encode x)))
      ((Data.cons (encode x) (encode x)).size + 1 + ((encode x).size + (encode x).size + 38) + 1) :=
  callVar_eval (i := 0) smnProg_wellScoped (v := .cons (encode x) (encode x)) (by simp)
    (smnProg_runs (encode x) (encode x))
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
open Polynomial
/-- The run of the final pairing step of `kleeneProg`. -/
theorem kleeneProg_pair2_eval (x : Prog) (v : Data) (F : PolyTimeFun Prog Prog) :
    Eval (encode (F (hardcode x (encode x))) :: encode (hardcode x (encode x)) ::
        [Data.cons (encode x) (encode x), encode x, v, Data.cons (encode x) v])
      (.cons (.var 0) (.var 4)) (.cons (encode (F (hardcode x (encode x)))) v)
      ((encode (F (hardcode x (encode x)))).size + 1 + (v.size + 1) + 1) :=
  Eval.cons (Eval.var_of_get (i := 0) (v := encode (F (hardcode x (encode x)))) (by simp))
    (Eval.var_of_get (i := 4) (v := v) (by simp))
end MIPRE.Cost.Prog

/-! The uploaded declaration, hoisted to the top level as `solution`. -/
open MIPRE
open MIPRE.Cost
open MIPRE.Cost.Prog
open Polynomial
theorem solution (U : UniversalMachine) (F : PolyTimeFun Prog Prog) (x : Prog)
    {v r : Data} {t : ℕ} (h : (F (hardcode x (encode x))).Runs v r t) :
    ∃ T ≤ 6 * esize x + esize (hardcode x (encode x)) +
        F.timeBound.eval (esize (hardcode x (encode x))) +
        2 * esize (F (hardcode x (encode x))) + 2 * v.size +
        U.bound.eval (esize (F (hardcode x (encode x))) + v.size + t) + 57,
      (kleeneProg U.univ F).Runs (.cons (encode x) v) r T := by
  obtain ⟨tF, htF, hF⟩ := F.computes (hardcode x (encode x))
  obtain ⟨tU, htU, hU⟩ := U.time_le _ v r t h
  have s3 := callVar_eval
    (env := encode (hardcode x (encode x)) ::
      [Data.cons (encode x) (encode x), encode x, v, Data.cons (encode x) v])
    (i := 0) F.closed (v := encode (hardcode x (encode x))) (by simp) hF
  have s5 := callVar_eval
    (env := Data.cons (encode (F (hardcode x (encode x)))) v ::
      encode (F (hardcode x (encode x))) :: encode (hardcode x (encode x)) ::
      [Data.cons (encode x) (encode x), encode x, v, Data.cons (encode x) v])
    (i := 0) U.closed (v := .cons (encode (F (hardcode x (encode x)))) v) (by simp) hU
  refine ⟨_, ?_, Eval.elim_cons (env := [Data.cons (encode x) v]) (i := 0) (n := .nil)
    (a := encode x) (b := v) (by simp)
    (Eval.let_ (kleeneProg_pair_eval x v) (Eval.let_ (kleeneProg_smn_eval x v)
      (Eval.let_ s3 (Eval.let_ (kleeneProg_pair2_eval x v F) s5))))⟩
  have e1 : (encode x).size = esize x := rfl
  have e2 : (encode (hardcode x (encode x))).size = esize (hardcode x (encode x)) := rfl
  have e3 : (encode (F (hardcode x (encode x)))).size = esize (F (hardcode x (encode x))) :=
    rfl
  simp only [Data.size_cons]
  omega
