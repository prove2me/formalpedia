-- Prove2me | solution 1 for MIPRE.sgn_add
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:35:06.819337+00:00
-- url     : https://prove2.me/submissions/86ef1bd4-dc55-4f67-bb1c-2b7cd1ab5df1

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Sign.lean (solution of MIPRE.sgn_add);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Sign

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE
theorem _root_.solution (x y : ZMod 2) : sgn (x + y) = sgn x * sgn y := by
  have hx : x.val < 2 := ZMod.val_lt x
  have hy : y.val < 2 := ZMod.val_lt y
  rw [sgn, sgn, sgn, ZMod.val_add]
  interval_cases h : x.val <;> interval_cases h2 : y.val <;> norm_num
end MIPRE
