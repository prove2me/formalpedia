-- Prove2me | solution 1 for MIPRE.Cost.hardcode_size
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-12T17:05:59.497794+00:00
-- url     : https://prove2.me/submissions/713a4dee-bb01-44bb-b84e-1118dd3187ea

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/Toolkit.lean (solution of MIPRE.Cost.hardcode_size);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context; each is used only by proofs. -/
namespace MIPRE.Cost.Prog
theorem esize_eq_size_toData (p : Prog) : esize p = p.toData.size := rfl
end MIPRE.Cost.Prog

namespace MIPRE.Cost
open Polynomial
/-- The description of a hardcoded program, spelled out. -/
theorem toData_hardcode (p : Prog) (d : Data) :
    (hardcode p d).toData = .cons (.ofNat 4) (.cons (.cons (.ofNat 2)
      (.cons (.cons (.ofNat 6) d) (.cons .nil .nil))) p.toData) := rfl
end MIPRE.Cost

/-! The uploaded declaration, hoisted to the top level as `solution`. -/
open MIPRE
open MIPRE.Cost
open Polynomial
theorem solution (p : Prog) (d : Data) :
    esize (hardcode p d) = esize p + d.size + 35 := by
  simp only [Prog.esize_eq_size_toData, toData_hardcode, Data.size_cons, Data.size_ofNat,
    Data.size_nil]
  omega
