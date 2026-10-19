-- Prove2me | solution 1 for MIPRE.Cost.Prog.repSampCore_prefix
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-16T15:36:17.681477+00:00
-- url     : https://prove2.me/submissions/7c8c089b-87f3-4add-9c1d-e8d7f698ead0

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Repeat/Sampler.lean (solution of MIPRE.Cost.Prog.repSampCore_prefix);
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

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.Cost.Prog
section
open Data
/-- The size of the encoded dimension query. -/
theorem size_encode_dimension : (encode CL.Sampler.Query.dimension : Data).size = 9 := rfl
end
end MIPRE.Cost.Prog

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Cost.Prog
open Data
theorem _root_.solution {univ : Prog} (hU : univ.WellScoped 1) (sD lD tD nD d : Data)
    {sz : Data} {td : ℕ}
    (hdim : Eval [Data.cons sD (.cons nD (encode CL.Sampler.Query.dimension))] univ sz td)
    {r : Data} {t : ℕ} (hc : Eval (coreEnv sD lD tD nD d sz) (coreDispatch univ) r t) :
    Eval [Data.cons (sampParams sD lD tD) (.cons nD d)] (repSampCore univ) r
      (t + td + 2 * (sD.size + nD.size) + 32) := by
  have run : Eval [Data.cons (sampParams sD lD tD) (.cons nD d)] (repSampCore univ) r _ :=
    Eval.elim_cons (env := [Data.cons (sampParams sD lD tD) (.cons nD d)]) (i := 0) (n := .nil)
      (a := sampParams sD lD tD) (b := .cons nD d) (by simp)
      (Eval.elim_cons (i := 0) (n := .nil) (a := sD) (b := .cons lD tD) (by simp [sampParams])
        (Eval.elim_cons (i := 1) (n := .nil) (a := lD) (b := tD) (by simp)
          (Eval.elim_cons (i := 5) (n := .nil) (a := nD) (b := d) (by simp)
            (Eval.let_ (Eval.cons (Eval.var_of_get (i := 4) (v := sD) (by simp))
                (Eval.cons (Eval.var_of_get (i := 0) (v := nD) (by simp)) (Eval.const _ _)))
              (Eval.let_ (callVar_eval hU (i := 0)
                  (v := .cons sD (.cons nD (encode CL.Sampler.Query.dimension))) (by simp) hdim)
                hc)))))
  refine run.cast_cost ?_
  simp only [size_cons, size_encode_dimension]
  omega
end MIPRE.Cost.Prog
