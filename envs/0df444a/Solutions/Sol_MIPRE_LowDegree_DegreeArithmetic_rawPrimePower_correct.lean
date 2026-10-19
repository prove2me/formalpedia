-- Prove2me | solution 1 for MIPRE.LowDegree.DegreeArithmetic.rawPrimePower_correct
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:23:30.226251+00:00
-- url     : https://prove2.me/submissions/9550ffc6-6968-4ef7-beb1-4f2e1f5058a3

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/UnaryPrimePower.lean (solution of MIPRE.LowDegree.DegreeArithmetic.rawPrimePower_correct);
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
import Definitions.Def_MIPRE_Foundations_LowDegree_UnaryPrimality
import Definitions.Def_MIPRE_Foundations_LowDegree_UnaryPrimePower

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LowDegree.DegreeArithmetic
open Cost Cost.PolyTimeFun Polynomial
theorem _root_.solution (n q : ℕ) (hq : q.Prime) :
    rawPrimePower (unary n) (unary q) = unary (q ^ n.factorization q) := by
  by_cases hn : n = 0
  · subst n
    simp [rawPrimePower, unary]
  · have hpos : 0 < n := Nat.pos_of_ne_zero hn
    have hd : q ^ n.factorization q ∣ n := (hq.pow_dvd_iff_le_factorization hn).mpr le_rfl
    have hpow := Nat.le_of_dvd hpos hd
    have htwo := Nat.pow_le_pow_left hq.two_le (n.factorization q)
    have hexp : n.factorization q < 2 ^ (n.factorization q) := Nat.lt_two_pow_self
    have hb : n.factorization q ≤ n := by omega
    rw [rawPrimePower, fold_primePowerStep, length_unary, iterate_primePowerStep n q n hpos hq,
      min_eq_right hb]
end MIPRE.LowDegree.DegreeArithmetic
