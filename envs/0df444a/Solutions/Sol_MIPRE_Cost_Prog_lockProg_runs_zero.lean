-- Prove2me | solution 1 for MIPRE.Cost.Prog.lockProg_runs_zero
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-16T15:35:55.476142+00:00
-- url     : https://prove2.me/submissions/4e25afda-006c-4792-9a35-ef10f9dbc43e

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Repeat/Sampler.lean (solution of MIPRE.Cost.Prog.lockProg_runs_zero);
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

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Cost.Prog
open Data
theorem _root_.solution (univ : Prog) (sD nD kD wD jD uD yD : Data) :
    ∃ t ≤ esize (0 : ℕ) + toUnaryCost 0 + sD.size + nD.size + kD.size + wD.size + jD.size +
        uD.size + yD.size + 30,
      Eval [lockInput sD nD (encode 0) kD wD jD uD yD] (lockProg univ) .nil t := by
  obtain ⟨t₁, ht₁, h₁⟩ := toUnaryProg_runs 0
  set inp := lockInput sD nD (encode 0) kD wD jD uD yD with hinp
  have run : Eval [inp] (lockProg univ) .nil _ :=
    Eval.elim_cons (env := [inp]) (i := 0) (n := .nil) (a := sD)
      (b := .cons nD (.cons (encode 0) (.cons kD (.cons wD (.cons jD (.cons uD yD))))))
      (by simp [hinp, lockInput])
      (Eval.elim_cons (i := 1) (n := .nil) (a := nD)
        (b := .cons (encode 0) (.cons kD (.cons wD (.cons jD (.cons uD yD))))) (by simp)
        (Eval.elim_cons (i := 1) (n := .nil) (a := encode 0)
          (b := .cons kD (.cons wD (.cons jD (.cons uD yD)))) (by simp)
          (Eval.elim_cons (i := 1) (n := .nil) (a := kD) (b := .cons wD (.cons jD (.cons uD yD)))
            (by simp)
            (Eval.elim_cons (i := 1) (n := .nil) (a := wD) (b := .cons jD (.cons uD yD)) (by simp)
              (Eval.elim_cons (i := 1) (n := .nil) (a := jD) (b := .cons uD yD) (by simp)
                (Eval.elim_cons (i := 1) (n := .nil) (a := uD) (b := yD) (by simp)
                  (Eval.let_ (callVar_eval toUnaryProg_wellScoped (i := 8) (v := encode 0) (by simp) h₁)
                    (Eval.elim_nil (i := 0) (by simp [ofNat]) (Eval.nil _)))))))))
  refine ⟨_, ?_, run⟩
  unfold toUnaryCost
  have : (encode 0 : Data).size = esize 0 := rfl
  simp only [this]
  omega
end MIPRE.Cost.Prog
