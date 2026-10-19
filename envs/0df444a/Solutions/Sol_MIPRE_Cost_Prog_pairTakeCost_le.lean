-- Prove2me | solution 1 for MIPRE.Cost.Prog.pairTakeCost_le
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-16T15:33:01.270361+00:00
-- url     : https://prove2.me/submissions/79ab357e-2c4e-4eed-a73a-8aa65a4b4603

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Repeat/MapLoop.lean (solution of MIPRE.Cost.Prog.pairTakeCost_le);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Computability.Primrec.List
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Logic.Denumerable
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
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

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Cost.Prog
open Data
theorem _root_.solution {s U Y Z : ℕ} (h : s + U + Y ≤ Z) :
    pairTakeCost s U Y ≤ 17 * (Z + 30) ^ 2 := by
  unfold pairTakeCost
  have h1 : (s + 1) * (U + Y + 2 * s + 21) ≤ (Z + 30) * (2 * (Z + 30)) :=
    Nat.mul_le_mul (by omega) (by omega)
  have e : (Z + 30) * (2 * (Z + 30)) = 2 * ((Z + 30) * (Z + 30)) := by ring
  rw [e] at h1
  have h2 : (U + 2) * (U + Y + 13) ≤ (Z + 30) * (Z + 30) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h3 : (Y + 2) * (U + Y + 13) ≤ (Z + 30) * (Z + 30) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h4 : 4 * s + 8 * U + 8 * Y + 40 ≤ 9 * ((Z + 30) * (Z + 30)) := by nlinarith
  rw [pow_two]
  omega
end MIPRE.Cost.Prog
