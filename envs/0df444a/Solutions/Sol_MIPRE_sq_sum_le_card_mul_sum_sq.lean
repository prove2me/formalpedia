-- Prove2me | solution 1 for MIPRE.sq_sum_le_card_mul_sum_sq
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:21:17.859046+00:00
-- url     : https://prove2.me/submissions/5da245c6-a394-4442-a9be-b945f2ea7aec

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Closeness.lean (solution of MIPRE.sq_sum_le_card_mul_sum_sq);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_Closeness

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE
open Finset ComplexOrder Matrix
variable {n : Type*} [Fintype n]
theorem _root_.solution {ι : Type*} [Fintype ι] (t : ι → ℝ) (ht : ∀ i, 0 ≤ t i) :
    (∑ i, t i) ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ i, t i ^ 2 := by
  have h1 : ∑ i, t i = ∑ i, √(1 : ℝ) * √(t i ^ 2) :=
    Finset.sum_congr rfl fun i _ => by rw [Real.sqrt_one, one_mul, Real.sqrt_sq (ht i)]
  have h2 := Real.sum_sqrt_mul_sqrt_le (Finset.univ : Finset ι) (f := fun _ => (1 : ℝ))
    (g := fun i => t i ^ 2) (fun _ => zero_le_one) (fun i => sq_nonneg _)
  rw [← h1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at h2
  have hs : (0 : ℝ) ≤ ∑ i, t i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  calc (∑ i, t i) ^ 2
      ≤ (√(Fintype.card ι : ℝ) * √(∑ i, t i ^ 2)) ^ 2 :=
        pow_le_pow_left₀ (Finset.sum_nonneg fun i _ => ht i) h2 2
    _ = (Fintype.card ι : ℝ) * ∑ i, t i ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), Real.sq_sqrt hs]
end MIPRE
