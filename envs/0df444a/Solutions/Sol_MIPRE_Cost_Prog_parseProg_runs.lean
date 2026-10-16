-- Prove2me | solution 1 for MIPRE.Cost.Prog.parseProg_runs
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-15T20:20:09.085931+00:00
-- url     : https://prove2.me/submissions/26faf22b-be60-4988-88b3-18c3186abda3

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Halting/Serial.lean (solution of MIPRE.Cost.Prog.parseProg_runs);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Computability.Primrec.List
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Logic.Denumerable
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Codable
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Halting_Descriptions
import Definitions.Def_MIPRE_Foundations_Cost_Numeric
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Halting_Lists
import Definitions.Def_MIPRE_Foundations_Halting_Serial
import Theorems.Thm_MIPRE_Cost_Prog_parseLoop_runs

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Cost.Prog
open Data
theorem _root_.solution (x : BitStr) :
    ∃ t ≤ (x.length + 2) * ((encode x : Data).size + 2 * x.length + 25),
      parseProg.Runs (encode x) (parse x) t := by
  obtain ⟨t, ht, hrun⟩ := parseLoop_runs x [] [encode x] ((encode x : Data).size + 2 * x.length + 1)
    (by simp only [list_nil, Data.size_nil]; omega)
  have hpre := Eval.cons (Eval.var_of_get (env := [encode x]) (i := 0) (v := encode x) (by simp))
    (Eval.nil [encode x])
  refine ⟨_, ?_, Eval.let_ hpre (by simpa [parse] using hrun)⟩
  have h2 : (x.length + 2) * ((encode x : Data).size + 2 * x.length + 25) =
      (x.length + 1) * ((encode x : Data).size + 2 * x.length + 25) +
        ((encode x : Data).size + 2 * x.length + 25) := Nat.succ_mul _ _
  have h3 : (x.length + 1) * ((encode x : Data).size + 2 * x.length + 1 + 21) ≤
      (x.length + 1) * ((encode x : Data).size + 2 * x.length + 25) :=
    Nat.mul_le_mul_left _ (by omega)
  omega
end MIPRE.Cost.Prog
