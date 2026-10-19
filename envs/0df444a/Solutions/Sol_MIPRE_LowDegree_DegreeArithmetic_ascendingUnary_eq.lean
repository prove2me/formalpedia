-- Prove2me | solution 1 for MIPRE.LowDegree.DegreeArithmetic.ascendingUnary_eq
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:18:29.95285+00:00
-- url     : https://prove2.me/submissions/6c63ccb3-0257-4c16-80f1-44eaf9c5a72e

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryDegreeDecomposition.lean (solution of MIPRE.LowDegree.DegreeArithmetic.ascendingUnary_eq);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.List.OfFn
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
import Definitions.Def_MIPRE_Foundations_LowDegree_UnaryPrimality
import Definitions.Def_MIPRE_Foundations_LowDegree_UnaryPrimePower
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryDegreeFactors
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryDegreeDecomposition

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LowDegree.DegreeArithmetic
open Cost Cost.PolyTimeFun
theorem _root_.solution (u : Unary) :
    ascendingUnary u = List.ofFn (fun i : Fin (u.length + 1) => unary (i : ℕ)) := by
  induction u with
  | nil => rfl
  | cons x u ih =>
    cases x
    rw [ascendingUnary, descendingUnary_cons, List.reverse_cons]
    change ascendingUnary u ++ [() :: u] = _
    rw [ih]
    conv_rhs => rw [List.ofFn_succ']
    simp only [Fin.val_castSucc, Fin.val_last, List.concat_eq_append]
    have hu : unary (u.length + 1) = () :: u := by
      change () :: unary u.length = () :: u
      rw [unary_length]
    simp only [List.length_cons]
    rw [hu]
end MIPRE.LowDegree.DegreeArithmetic
