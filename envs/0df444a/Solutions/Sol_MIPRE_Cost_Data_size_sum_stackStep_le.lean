-- Prove2me | solution 1 for MIPRE.Cost.Data.size_sum_stackStep_le
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-15T20:12:39.896138+00:00
-- url     : https://prove2.me/submissions/8e53a893-1254-495b-ab33-ff0646829c3b

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Halting/Descriptions.lean (solution of MIPRE.Cost.Data.size_sum_stackStep_le);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Computability.Primrec.List
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Logic.Denumerable
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
import Definitions.Def_MIPRE_Foundations_Halting_Descriptions

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Cost.Data
theorem _root_.solution (s : List Data) (bit : Bool) :
    ((stackStep s bit).map size).sum ≤ (s.map size).sum + 1 := by
  cases bit
  · simp only [stackStep_false, List.map_cons, List.sum_cons, size_nil]
    omega
  · by_cases h : 2 ≤ s.length
    · obtain ⟨b, a, t, rfl⟩ : ∃ b a t, s = b :: a :: t := by
        match s with
        | [] => simp at h
        | [_] => simp at h
        | b :: a :: t => exact ⟨b, a, t, rfl⟩
      simp only [stackStep_true_cons_cons, List.map_cons, List.sum_cons, size_cons]
      omega
    · simp [stackStep, h]
end MIPRE.Cost.Data
