-- Prove2me | solution 1 for MIPRE.SAT.PcpAlgebra.degreeOf_constraint_le
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:50:14.108726+00:00
-- url     : https://prove2.me/submissions/9d1ec551-0187-4971-af2e-4a4dfa282b16

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/SAT/PcpAlgebra.lean (solution of MIPRE.SAT.PcpAlgebra.degreeOf_constraint_le);
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
theorem _root_.solution (φ : MvPolynomial (Fin m) F)
    (g : Fin 5 → MvPolynomial (Fin m) F) (sign : Fin 5 → Fin m) {d : ℕ}
    (hφ : ∀ j, φ.degreeOf j ≤ 6) (hg : ∀ i j, (g i).degreeOf j ≤ d) (j : Fin m) :
    (constraint φ g sign).degreeOf j ≤ 6 + 5 * max d 1 := by
  apply (degreeOf_mul_le j _ _).trans
  apply Nat.add_le_add (hφ j)
  apply (degreeOf_prod_le j univ _).trans
  calc
    (∑ i : Fin 5, (g i - X (sign i)).degreeOf j) ≤ ∑ _i : Fin 5, max d 1 := by
      apply Finset.sum_le_sum
      intro i _
      apply (degreeOf_sub_le j _ _).trans
      apply max_le_max (hg i j)
      by_cases h : j = sign i
      · simp [h]
      · simp [degreeOf_X_of_ne h]
    _ = 5 * max d 1 := by simp
end MIPRE.SAT.PcpAlgebra
