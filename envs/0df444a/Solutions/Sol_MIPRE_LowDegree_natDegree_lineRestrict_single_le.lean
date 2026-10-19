-- Prove2me | solution 1 for MIPRE.LowDegree.natDegree_lineRestrict_single_le
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:46:27.41303+00:00
-- url     : https://prove2.me/submissions/bd3bef56-cd83-4d3e-a7d1-752055b5dcbf

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/LineRestrict.lean (solution of MIPRE.LowDegree.natDegree_lineRestrict_single_le);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Degree
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_LowDegree_LineRestrict

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LowDegree
open Finset
variable {F : Type*} [Field F] {m : ℕ}
theorem _root_.solution (u₀ : Fin m → F) (j : Fin m)
    (p : MvPolynomial (Fin m) F) :
    (lineRestrict u₀ (Pi.single j 1) p).natDegree ≤ p.degreeOf j := by
  classical
  rw [lineRestrict, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun dd hdd => ?_
  refine le_trans Polynomial.natDegree_mul_le ?_
  have h0 : (algebraMap F (Polynomial F) (MvPolynomial.coeff dd p)).natDegree = 0 := by
    simp [Polynomial.algebraMap_eq]
  rw [h0, zero_add]
  have hterm : ∀ i : Fin m,
      (((Polynomial.C (u₀ i) + Polynomial.X
          * Polynomial.C ((Pi.single j 1 : Fin m → F) i)) ^ dd i) : Polynomial F).natDegree
        ≤ if i = j then dd i else 0 := by
    intro i
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl]
      refine le_trans Polynomial.natDegree_pow_le ?_
      refine le_trans (Nat.mul_le_mul_left _ ?_) (le_of_eq (mul_one _))
      refine le_trans (Polynomial.natDegree_add_le _ _) (max_le (by simp) ?_)
      exact le_trans Polynomial.natDegree_mul_le (by simp)
    · rw [if_neg hij, Pi.single_eq_of_ne hij, map_zero, mul_zero, add_zero, ← Polynomial.C_pow,
        Polynomial.natDegree_C]
  refine le_trans (le_trans (Polynomial.natDegree_prod_le _ _)
    (Finset.sum_le_sum fun i _ => hterm i)) ?_
  rw [Finset.sum_ite_eq' dd.support j (fun i => dd i)]
  by_cases hj : j ∈ dd.support
  · rw [if_pos hj]
    exact MvPolynomial.monomial_le_degreeOf j hdd
  · rw [if_neg hj]
    exact Nat.zero_le _
end MIPRE.LowDegree
