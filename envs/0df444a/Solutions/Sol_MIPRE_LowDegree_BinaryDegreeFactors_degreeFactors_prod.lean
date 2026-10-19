-- Prove2me | solution 1 for MIPRE.LowDegree.BinaryDegreeFactors.degreeFactors_prod
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:45:11.31699+00:00
-- url     : https://prove2.me/submissions/66bcd745-e087-418c-b374-f04c3959e3d3

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryDegreeFactors.lean (solution of MIPRE.LowDegree.BinaryDegreeFactors.degreeFactors_prod);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Factorization.Basic
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryDegreeFactors

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LowDegree.BinaryDegreeFactors
theorem _root_.solution (n : ℕ) (hn : 0 < n) : (degreeFactors n).prod = n := by
  rw [degreeFactors, List.prod_ofFn,
    Fin.prod_univ_eq_prod_range (fun i => i ^ n.factorization i)]
  have hs : n.primeFactors ⊆ Finset.range (n + 1) := by
    intro p hp
    exact Finset.mem_range.mpr (by have := Nat.le_of_mem_primeFactors hp; omega)
  have he : (∏ p ∈ n.primeFactors, p ^ n.factorization p) =
      ∏ p ∈ Finset.range (n + 1), p ^ n.factorization p := by
    apply Finset.prod_subset hs
    intro p _ hp
    have hz : n.factorization p = 0 := Finsupp.notMem_support_iff.mp hp
    simp [hz]
  rw [← he, ← Nat.prod_primeFactors_pow_factorization hn.ne']
end MIPRE.LowDegree.BinaryDegreeFactors
