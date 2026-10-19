-- Prove2me | solution 1 for MIPRE.SAT.Circuit.valueAt_eq
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:49:08.988607+00:00
-- url     : https://prove2.me/submissions/dd54059c-98da-47c9-93ce-b2073907371a

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/SAT/Circuit.lean (solution of MIPRE.SAT.Circuit.valueAt_eq);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.SAT.Circuit
open Cost
theorem _root_.solution (C : Circuit) (x : ℕ → Bool) (g : ℕ) :
    C.valueAt x g = (C.gates.getD g (.const false)).eval x (List.ofFn fun k : Fin g => C.valueAt x k) := by
  rw [valueAt]
end MIPRE.SAT.Circuit
