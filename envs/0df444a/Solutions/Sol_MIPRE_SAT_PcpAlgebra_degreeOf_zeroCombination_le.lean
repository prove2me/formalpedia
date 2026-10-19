-- Prove2me | solution 1 for MIPRE.SAT.PcpAlgebra.degreeOf_zeroCombination_le
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:50:57.691799+00:00
-- url     : https://prove2.me/submissions/ab087024-dcdd-4906-995c-49c49d113104

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/SAT/PcpAlgebra.lean (solution of MIPRE.SAT.PcpAlgebra.degreeOf_zeroCombination_le);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Combinatorics.Nullstellensatz
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_ZeroBasis
import Definitions.Def_MIPRE_Foundations_SAT_PcpAlgebra

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.SAT.PcpAlgebra
open Finset MvPolynomial LowDegree
variable {F : Type*} [Field F] {m : ℕ}
theorem _root_.solution (c : Fin m → MvPolynomial (Fin m) F) {d : ℕ}
    (hc : ∀ i j, (c i).degreeOf j ≤ d) (j : Fin m) :
    (zeroCombination c).degreeOf j ≤ d + 2 := by
  apply (degreeOf_sum_le j univ _).trans
  apply Finset.sup_le
  intro i _
  apply (degreeOf_mul_le j _ _).trans
  apply Nat.add_le_add (hc i j)
  have hx : (X i : MvPolynomial (Fin m) F).degreeOf j ≤ 1 := by
    by_cases h : j = i
    · simp [h]
    · simp [degreeOf_X_of_ne h]
  exact (degreeOf_mul_le j _ _).trans
    (Nat.add_le_add hx ((degreeOf_sub_le j 1 (X i)).trans (by simpa using hx)))
end MIPRE.SAT.PcpAlgebra
