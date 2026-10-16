-- Prove2me | solution 1 for MIPRE.Cost.Data.canonWalk_eq_isCanonBin
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-15T20:18:24.276815+00:00
-- url     : https://prove2.me/submissions/3f98fd8c-9adb-4c35-ac6a-248525b6d860

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Halting/Lists.lean (solution of MIPRE.Cost.Data.canonWalk_eq_isCanonBin);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Computability.Primrec.List
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Logic.Denumerable
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
import Theorems.Thm_MIPRE_Cost_Data_canonWalk_iff
import Theorems.Thm_MIPRE_Cost_Data_encode_of_decode_bitStr

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Cost.Data
theorem _root_.solution (d : Data) : canonWalk d true = isCanonBin d := by
  rcases hc : isCanonBin d
  · rw [← Bool.not_eq_true, canonWalk_iff]
    rintro ⟨l, rfl, h1, h2⟩
    have : isCanonBin (encode l) = true := by
      simp only [isCanonBin]
      show (match (decode (encode l) : Option BitStr) with
        | some l => decide (l = [] ∨ l.getLast? = some true)
        | none => false) = true
      rw [SizedEncoding.decode_encode]
      by_cases hl : l = []
      · simp [hl]
      · simp [h2 hl]
    rw [hc] at this; exact absurd this Bool.false_ne_true
  · rw [canonWalk_iff]
    unfold isCanonBin at hc
    rcases hdec : (decode d : Option BitStr) with _ | l
    · rw [hdec] at hc; simp at hc
    · rw [hdec] at hc
      refine ⟨l, (encode_of_decode_bitStr hdec).symm, fun _ => rfl, fun hne => ?_⟩
      simp only [decide_eq_true_eq] at hc
      rcases hc with hc | hc
      · exact absurd hc hne
      · exact hc
end MIPRE.Cost.Data
