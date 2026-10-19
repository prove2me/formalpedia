-- Prove2me | solution 1 for MIPRE.LowDegree.BinaryFiniteField.mem_range_iff_pow_card
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:45:43.616277+00:00
-- url     : https://prove2.me/submissions/3d274b87-013a-45bc-b8f0-2dd3e9c37f22

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryFiniteFieldDegree.lean (solution of MIPRE.LowDegree.BinaryFiniteField.mem_range_iff_pow_card);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.FieldTheory.Finite.Extension

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LowDegree.BinaryFiniteField
open Polynomial
theorem _root_.solution {K L : Type*} [Field K] [Field L] [Finite K]
    [Algebra K L] (x : L) :
    x ∈ (algebraMap K L).range ↔ x ^ Nat.card K = x := by
  constructor
  · rintro ⟨y, rfl⟩
    have : Fintype K := Fintype.ofFinite K
    rw [← map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card]
  · intro hx
    apply (Polynomial.splits_X_pow_nat_card_sub_X (K := K)).mem_range_of_isRoot
      (FiniteField.X_pow_card_sub_X_ne_zero K (Finite.one_lt_card))
    change eval x ((X ^ Nat.card K - X : K[X]).map (algebraMap K L)) = 0
    rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, eval_sub,
      eval_pow, eval_X, sub_eq_zero]
    exact hx
end MIPRE.LowDegree.BinaryFiniteField
