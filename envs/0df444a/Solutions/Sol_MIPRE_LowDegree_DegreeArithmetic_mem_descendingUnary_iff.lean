-- Prove2me | solution 1 for MIPRE.LowDegree.DegreeArithmetic.mem_descendingUnary_iff
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:44:10.609864+00:00
-- url     : https://prove2.me/submissions/958d4fa6-0773-49b5-814b-dafec29a3be3

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/UnaryDegreeArithmetic.lean (solution of MIPRE.LowDegree.DegreeArithmetic.mem_descendingUnary_iff);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Linarith
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_Cost_Iterates
import Definitions.Def_MIPRE_Foundations_LowDegree_UnaryDegreeArithmetic

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.LowDegree.DegreeArithmetic
noncomputable section
open Cost Cost.PolyTimeFun Polynomial
/-- The enumeration consists exactly of the successive suffixes. -/
theorem descendingUnary_eq (u : Unary) :
    descendingUnary u = List.ofFn (fun i : Fin (u.length + 1) => u.drop i) := by
  simp [descendingUnary, recordIterates, List.tail_iterate]
end
end MIPRE.LowDegree.DegreeArithmetic

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LowDegree.DegreeArithmetic
open Cost Cost.PolyTimeFun Polynomial
theorem _root_.solution (u d : Unary) : d ∈ descendingUnary u ↔ d.length ≤ u.length := by
  rw [descendingUnary_eq, List.mem_ofFn]
  constructor
  · rintro ⟨i, rfl⟩
    simp
  · intro h
    refine ⟨⟨u.length - d.length, by omega⟩, ?_⟩
    apply List.ext_getElem
    · simp only [List.length_drop]
      omega
    · intro i hi hj
      exact Subsingleton.elim _ _
end MIPRE.LowDegree.DegreeArithmetic
