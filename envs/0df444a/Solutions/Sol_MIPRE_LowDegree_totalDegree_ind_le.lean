-- Prove2me | solution 1 for MIPRE.LowDegree.totalDegree_ind_le
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:28:08.210274+00:00
-- url     : https://prove2.me/submissions/c5c223bb-5b7e-4944-8daa-6fafe9e9f271

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/Encoding.lean (solution of MIPRE.LowDegree.totalDegree_ind_le);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LowDegree
open Finset MvPolynomial
variable {F : Type*} [CommRing F] {m : ℕ}
theorem _root_.solution [Nontrivial F] (y : Fin m → Bool) :
    (ind y : MvPolynomial (Fin m) F).totalDegree ≤ m := by
  have hfac : ∀ j : Fin m,
      (if y j then (X j : MvPolynomial (Fin m) F) else 1 - X j).totalDegree ≤ 1 := by
    intro j
    cases hy : y j
    · simp only [Bool.false_eq_true, if_false]
      exact le_trans (MvPolynomial.totalDegree_sub 1 (X j)) (by simp)
    · simp
  rw [ind]
  refine le_trans (MvPolynomial.totalDegree_finsetProd _ _) ?_
  refine le_trans (Finset.sum_le_sum fun j _ => hfac j) ?_
  simp
end MIPRE.LowDegree
