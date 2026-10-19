-- Prove2me | solution 1 for MIPRE.SAT.Circuit.lastInputValue_range
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:25:10.526351+00:00
-- url     : https://prove2.me/submissions/6b6d98d0-0b6e-4381-ab33-08bceea765e3

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/SAT/InputRoutingProg.lean (solution of MIPRE.SAT.Circuit.lastInputValue_range);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Set.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_SAT_Cnf
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_SAT_Flatten
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_SAT_FmlProg
import Definitions.Def_MIPRE_Foundations_SAT_ArrayProg
import Definitions.Def_MIPRE_Foundations_SAT_Tseitin
import Definitions.Def_MIPRE_Foundations_SAT_GateProg
import Definitions.Def_MIPRE_Foundations_SAT_InputRouting
import Definitions.Def_MIPRE_Foundations_SAT_InputRoutingProg

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.SAT.Circuit
open Cost Cost.PolyTimeFun Polynomial
variable {α : Type*} [SizedEncoding α]
theorem _root_.solution (C : Circuit) (k i : ℕ) (x w : ℕ → α) :
    lastInputValue ((List.range k).map (fun j => (C.gates.getD j (.const false), w j)))
      i (x i) = Sum.elim x w (C.inputRef k i) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.map_append, lastInputValue_append]
    change (if C.gates.getD k (.const false) = .input i then w k else
      lastInputValue ((List.range k).map (fun j => (C.gates.getD j (.const false), w j)))
        i (x i)) = _
    rw [ih]
    by_cases h : C.gates.getD k (.const false) = .input i
    · simp only [inputRef, inputOwner]; simp only [h, if_true]; simp
    · simp only [inputRef, inputOwner]; simp only [h, if_false]
end MIPRE.SAT.Circuit
