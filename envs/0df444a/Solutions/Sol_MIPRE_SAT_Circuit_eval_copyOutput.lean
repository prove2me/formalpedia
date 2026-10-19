-- Prove2me | solution 1 for MIPRE.SAT.Circuit.eval_copyOutput
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:24:50.43016+00:00
-- url     : https://prove2.me/submissions/2297439b-597b-48ae-8d65-1c94621bd95d

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/SAT/GatePadding.lean (solution of MIPRE.SAT.Circuit.eval_copyOutput);
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
import Definitions.Def_MIPRE_Foundations_SAT_GatePadding
import Theorems.Thm_MIPRE_SAT_Circuit_valueAt_eq

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.SAT.Fml
section
open Cost
/-- The value of a gate depends only on the gates up to it: appending gates changes nothing. -/
theorem Circuit.valueAt_append (n : ℕ) (gs post : List Gate) (x : ℕ → Bool) (k : ℕ)
    (hk : k < gs.length) :
    (Circuit.mk n (gs ++ post)).valueAt x k = (Circuit.mk n gs).valueAt x k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rw [Circuit.valueAt_eq, Circuit.valueAt_eq]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left hk]
    congr 1
    congr 1
    funext i
    exact ih i i.isLt (lt_trans i.isLt hk)
end
end MIPRE.SAT.Fml

namespace MIPRE.SAT.Fml
section
open Cost
/-- The values of the earlier gates, as read by a gate. -/
theorem Circuit.getD_ofFn_valueAt (C : Circuit) (x : ℕ → Bool) (k u : ℕ) (hu : u < k) :
    (List.ofFn fun i : Fin k => C.valueAt x i).getD u false = C.valueAt x u := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hu]
  rfl
end
end MIPRE.SAT.Fml

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.SAT.Circuit
open Cost Cost.PolyTimeFun
theorem _root_.solution (C : Circuit) (hne : C.gates ≠ []) (x : ℕ → Bool) :
    (copyOutput C).eval x = C.eval x := by
  have hlen : 0 < C.gates.length := List.length_pos_iff.mpr hne
  have hne' : (copyOutput C).gates ≠ [] := by simp [copyOutput]
  rw [Circuit.eval, if_neg hne', Circuit.eval, if_neg hne]
  change (copyOutput C).valueAt x ((C.gates ++ [_]).length - 1) = _
  simp only [List.length_append, List.length_singleton, Nat.add_sub_cancel]
  rw [Circuit.valueAt_eq]
  change ((C.gates ++ [_]).getD C.gates.length (.const false)).eval x _ = _
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), Nat.sub_self]
  simp only [List.getElem?_cons_zero, Option.getD_some, Gate.eval]
  rw [Fml.Circuit.getD_ofFn_valueAt _ _ _ _ (by omega), Bool.or_self]
  exact Fml.Circuit.valueAt_append _ _ _ _ _ (by omega)
end MIPRE.SAT.Circuit
