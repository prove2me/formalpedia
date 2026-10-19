-- Prove2me | solution 1 for MIPRE.Cost.esize_list_reverse
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:42:49.043333+00:00
-- url     : https://prove2.me/submissions/63206f03-9e2a-4a93-bc09-1e8ba1d2e2b5

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/Fold.lean (solution of MIPRE.Cost.esize_list_reverse);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Cost
open Polynomial
variable {α : Type*} [SizedEncoding α]
theorem _root_.solution (l : List α) : esize l.reverse = esize l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have := esize_list_append l.reverse [a]
    simp only [List.reverse_cons, esize_list_cons, esize_list_nil] at this ⊢
    omega
end MIPRE.Cost
