-- Prove2me | solution 1 for MIPRE.Cost.Data.encode_of_decode_bitStr
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-15T20:13:08.238736+00:00
-- url     : https://prove2.me/submissions/6261f34b-8119-4e40-98a7-8c3049d4794d

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Halting/Descriptions.lean (solution of MIPRE.Cost.Data.encode_of_decode_bitStr);
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
theorem _root_.solution {d : Data} {l : BitStr}
    (h : (decode d : Option BitStr) = some l) : (encode l : Data) = d := by
  induction d generalizing l with
  | nil =>
    simp only [SizedEncoding.decode, toList?, Option.some.injEq] at h
    subst h; rfl
  | cons a b _ ihb =>
    change toList? toBool? (cons a b) = some l at h
    change ∀ {l : BitStr}, toList? toBool? b = some l → encode l = b at ihb
    simp only [toList?] at h
    rw [toBool?_eq] at h
    split_ifs at h with ha ha'
    · subst ha
      rcases hb : toList? toBool? b with _ | l'
      · rw [hb] at h; simp at h
      · rw [hb] at h
        simp at h
        subst h
        change cons (ofBool _) (encode l') = _
        rw [ihb hb]; rfl
    · subst ha'
      rcases hb : toList? toBool? b with _ | l'
      · rw [hb] at h; simp at h
      · rw [hb] at h
        simp at h
        subst h
        change cons (ofBool _) (encode l') = _
        rw [ihb hb]; rfl
    · simp at h
end MIPRE.Cost.Data
