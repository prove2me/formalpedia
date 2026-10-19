-- Prove2me | solution 1 for MIPRE.Cost.Prog.coreDispatch_dim
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-16T15:37:23.632066+00:00
-- url     : https://prove2.me/submissions/52643b16-a309-4848-b1f4-944ad62f716c

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Repeat/Sampler.lean (solution of MIPRE.Cost.Prog.coreDispatch_dim);
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
theorem powBody_wellScoped : powBody.WellScoped 1 := by
  simp [powBody, WellScoped, lenBody]
end
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
section
open Data
theorem dimProg_wellScoped : dimProg.WellScoped 1 := by
  simp only [dimProg, WellScoped, callVar]
  refine ⟨by omega, trivial, by omega, trivial, by omega, trivial, by omega, trivial,
    ⟨by omega, toUnaryProg_wellScoped.mono (by omega) _⟩,
    ⟨by omega, by omega, by omega, by omega⟩, by omega, powBody_wellScoped.mono (by omega) _⟩
end
end MIPRE.Cost.Prog

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Cost.Prog
open Data
theorem _root_.solution (univ : Prog) (sD lD tD nD qr sz : Data) {r : Data} {t : ℕ}
    (hd : Eval [Data.cons sz (.cons lD (.cons nD tD))] dimProg r t) :
    Eval (coreEnv sD lD tD nD (.cons .nil qr) sz) (coreDispatch univ) r
      (t + 2 * (sz.size + lD.size + nD.size + tD.size) + 15) := by
  have run : Eval (coreEnv sD lD tD nD (.cons .nil qr) sz) (coreDispatch univ) r _ :=
    Eval.elim_cons (i := 3) (n := .nil) (a := .nil) (b := qr) (by simp [coreEnv])
      (Eval.elim_nil (i := 0) (by simp)
        (Eval.let_ (Eval.cons (Eval.var_of_get (i := 2) (v := sz) (by simp [coreEnv]))
            (Eval.cons (Eval.var_of_get (i := 6) (v := lD) (by simp [coreEnv]))
              (Eval.cons (Eval.var_of_get (i := 4) (v := nD) (by simp [coreEnv]))
                (Eval.var_of_get (i := 7) (v := tD) (by simp [coreEnv])))))
          (callVar_eval dimProg_wellScoped (i := 0) (v := .cons sz (.cons lD (.cons nD tD)))
            (by simp) hd)))
  refine run.cast_cost ?_
  simp only [size_cons]
  omega
end MIPRE.Cost.Prog
