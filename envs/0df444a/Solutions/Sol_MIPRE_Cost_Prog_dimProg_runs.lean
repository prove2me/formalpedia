-- Prove2me | solution 1 for MIPRE.Cost.Prog.dimProg_runs
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-16T15:35:46.278471+00:00
-- url     : https://prove2.me/submissions/e36aa171-d2f7-46fe-bb48-10ce9d50ef9f

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Repeat/Sampler.lean (solution of MIPRE.Cost.Prog.dimProg_runs);
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
import Theorems.Thm_MIPRE_Cost_Prog_powLoop_runs

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Cost.Prog
open Data
theorem _root_.solution (tau : ℕ) (bl bn : List Data) (h : Data) (l : List Data) :
    ∃ t ≤ dimCost tau (bl.length + bn.length) (list bl).size (list bn).size (list (h :: l)).size,
      Eval [Data.cons (list (h :: l)) (.cons (list bl) (.cons (list bn) (encode tau)))] dimProg
        (list (List.replicate (tau * (bl.length + bn.length)) .nil ++ (h :: l))) t := by
  set inp : Data := .cons (list (h :: l)) (.cons (list bl) (.cons (list bn) (encode tau))) with hinp
  set r2 : Data := .cons (list bn) (encode tau) with hr2
  set r : Data := .cons (list bl) r2 with hr
  obtain ⟨t₁, ht₁, h₁⟩ := toUnaryProg_runs tau
  obtain ⟨t₂, ht₂, h₂⟩ := powLoop_runs tau bl bn (h :: l)
    [ofNat tau, list bn, encode tau, list bl, r2, h, list l, list (h :: l), r, inp]
  have run : Eval [inp] dimProg (list (List.replicate (tau * (bl.length + bn.length)) .nil ++ (h :: l))) _ :=
    Eval.elim_cons (env := [inp]) (i := 0) (n := .nil) (a := list (h :: l)) (b := r)
      (by simp [hinp, hr, hr2])
      (Eval.elim_cons (i := 0) (n := .nil) (a := h) (b := list l) (by simp)
        (Eval.elim_cons (i := 3) (n := .nil) (a := list bl) (b := r2) (by simp [hr])
          (Eval.elim_cons (i := 1) (n := .nil) (a := list bn) (b := encode tau) (by simp [hr2])
            (Eval.let_ (callVar_eval toUnaryProg_wellScoped (i := 1) (v := encode tau) (by simp) h₁)
              (Eval.let_ (Eval.cons (Eval.var_of_get (i := 0) (v := ofNat tau) (by simp))
                  (Eval.cons (Eval.var_of_get (i := 3) (v := list bl) (by simp))
                    (Eval.cons (Eval.var_of_get (i := 1) (v := list bn) (by simp))
                      (Eval.var_of_get (i := 7) (v := list (h :: l)) (by simp)))))
                h₂)))))
  refine ⟨_, ?_, run⟩
  unfold dimCost toUnaryCost
  have : (encode tau : Data).size = esize tau := rfl
  simp only [size_ofNat, this]
  omega
end MIPRE.Cost.Prog
