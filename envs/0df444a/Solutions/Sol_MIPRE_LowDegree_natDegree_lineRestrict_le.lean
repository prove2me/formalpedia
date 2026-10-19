-- Prove2me | solution 1 for MIPRE.LowDegree.natDegree_lineRestrict_le
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:46:09.103393+00:00
-- url     : https://prove2.me/submissions/79dd66e9-e767-4f95-a77f-6cf62c970572

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/LineRestrict.lean (solution of MIPRE.LowDegree.natDegree_lineRestrict_le);
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
theorem _root_.solution (u₀ w : Fin m → F) (p : MvPolynomial (Fin m) F) :
    (lineRestrict u₀ w p).natDegree ≤ p.totalDegree := by
  have hlin : ∀ a b : F, (Polynomial.C a + Polynomial.X * Polynomial.C b).natDegree ≤ 1 := by
    intro a b
    refine le_trans (Polynomial.natDegree_add_le _ _) (max_le (by simp) ?_)
    exact le_trans Polynomial.natDegree_mul_le (by simp)
  rw [lineRestrict, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun d hd => ?_
  refine le_trans (Polynomial.natDegree_mul_le) ?_
  have h0 : (algebraMap F (Polynomial F) (MvPolynomial.coeff d p)).natDegree = 0 := by
    simp [Polynomial.algebraMap_eq]
  rw [h0, zero_add]
  refine le_trans (Polynomial.natDegree_prod_le _ _) ?_
  refine le_trans (Finset.sum_le_sum fun i _ => ?_) (MvPolynomial.le_totalDegree hd)
  calc ((Polynomial.C (u₀ i) + Polynomial.X * Polynomial.C (w i)) ^ d i).natDegree
      ≤ d i * (Polynomial.C (u₀ i) + Polynomial.X * Polynomial.C (w i)).natDegree :=
        Polynomial.natDegree_pow_le
    _ ≤ d i * 1 := Nat.mul_le_mul_left _ (hlin _ _)
    _ = d i := mul_one _
end MIPRE.LowDegree
