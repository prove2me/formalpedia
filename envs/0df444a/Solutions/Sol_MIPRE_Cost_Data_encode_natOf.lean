-- Prove2me | solution 1 for MIPRE.Cost.Data.encode_natOf
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-15T20:14:11.500145+00:00
-- url     : https://prove2.me/submissions/b7ef7bfa-9f61-4ddf-8627-363a8517402d

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Halting/Descriptions.lean (solution of MIPRE.Cost.Data.encode_natOf);
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
import Theorems.Thm_MIPRE_Cost_Data_encode_of_decode_bitStr

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Cost.Data
theorem _root_.solution (d : Data) : (encode (natOf d) : Data) = normBin d := by
  unfold natOf normBin
  split_ifs with h
  · unfold isCanonBin at h
    rcases hdec : (decode d : Option BitStr) with _ | l
    · rw [hdec] at h; simp at h
    · rw [hdec] at h
      have hl : l = [] ∨ l.getLast? = some true := by simpa using h
      have hdn : (decode d : Option ℕ) = some (l.foldr Nat.bit 0) := by
        show ((decode d : Option BitStr).map fun l => l.foldr Nat.bit 0) = _
        rw [hdec]; rfl
      rw [hdn, Option.getD_some]
      show encode (l.foldr Nat.bit 0).bits = d
      rw [bits_foldr_of_canon l hl]
      exact encode_of_decode_bitStr hdec
  · rfl
end MIPRE.Cost.Data
