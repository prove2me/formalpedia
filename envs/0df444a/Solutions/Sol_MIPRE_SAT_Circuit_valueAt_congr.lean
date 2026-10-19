-- Prove2me | solution 1 for MIPRE.SAT.Circuit.valueAt_congr
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:52:36.333828+00:00
-- url     : https://prove2.me/submissions/5ae5c5d0-cb54-47be-b3f7-885218f7f919

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/SAT/Tseitin.lean (solution of MIPRE.SAT.Circuit.valueAt_congr);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Set.Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_SAT_Cnf
import Definitions.Def_MIPRE_Foundations_SAT_Tseitin
import Theorems.Thm_MIPRE_SAT_Circuit_valueAt_eq

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.SAT.Circuit
variable {V : Type*}
theorem _root_.solution (C : Circuit) (hin : C.InputsLt) (x x' : ℕ → Bool)
    (hx : ∀ i < C.inputs, x i = x' i) : ∀ g, C.valueAt x g = C.valueAt x' g := by
  intro g
  induction g using Nat.strong_induction_on with
  | _ g ih =>
    rw [valueAt_eq, valueAt_eq]
    have hl : (List.ofFn fun k : Fin g => C.valueAt x k) = List.ofFn fun k : Fin g => C.valueAt x' k := by
      congr 1
      funext k
      exact ih k k.isLt
    rw [hl]
    by_cases hg : g < C.gates.length
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hg, Option.getD_some]
      cases hgate : C.gates[g] with
      | input i =>
        simp only [Gate.eval]
        exact hx i (hin i (hgate ▸ List.getElem_mem hg))
      | const b => rfl
      | and u v => rfl
      | or u v => rfl
      | not u => rfl
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      rfl
end MIPRE.SAT.Circuit
