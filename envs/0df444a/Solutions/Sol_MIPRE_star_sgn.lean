-- Prove2me | solution 1 for MIPRE.star_sgn
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:35:39.956905+00:00
-- url     : https://prove2.me/submissions/081ed68a-4a8a-4c9a-8090-c32189b7d80b

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Sign.lean (solution of MIPRE.star_sgn);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Sign

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE
theorem _root_.solution (x : ZMod 2) : star (sgn x) = sgn x := by
  rw [sgn]; split_ifs <;> norm_num
end MIPRE
