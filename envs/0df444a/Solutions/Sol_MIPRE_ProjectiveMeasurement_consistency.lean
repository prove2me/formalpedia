-- Prove2me | solution 1 for MIPRE.ProjectiveMeasurement.consistency
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:44:57.222661+00:00
-- url     : https://prove2.me/submissions/d2d9fdc0-8586-43e8-ba49-49610ec95402

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Games.lean (solution of MIPRE.ProjectiveMeasurement.consistency);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Definitions.Def_MIPRE_Foundations_Games

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.TracialState
section
open ComplexOrder Kronecker Matrix
open scoped MatrixOrder
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {𝒜 ℬ : Type*} [Ring 𝒜] [StarRing 𝒜] [Module ℂ 𝒜]
  [Ring ℬ] [StarRing ℬ] [Module ℂ ℬ]
/-- The trace of a product of two projections is nonnegative:
`τ (p * q) = τ (star (q * p) * (q * p))`. This is the positivity of outcome
probabilities for the strategies below. -/
theorem nonneg_mul (τ : TracialState 𝒜) {p q : 𝒜} (hps : star p = p) (hpp : p * p = p)
    (hqs : star q = q) (hqq : q * q = q) : 0 ≤ τ (p * q) := by
  have key : star (q * p) * (q * p) = p * q * p := by
    rw [star_mul, hps, hqs, mul_assoc p q (q * p), ← mul_assoc q q p, hqq, ← mul_assoc]
  calc (0 : ℂ) ≤ τ (star (q * p) * (q * p)) := τ.star_mul_self_nonneg _
    _ = τ (p * q * p) := by rw [key]
    _ = τ (p * q) := by rw [τ.map_mul_comm (p * q) p, ← mul_assoc, hpp]
end
end MIPRE.TracialState

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.ProjectiveMeasurement
open ComplexOrder Kronecker Matrix
open scoped MatrixOrder
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {𝒜 ℬ : Type*} [Ring 𝒜] [StarRing 𝒜] [Module ℂ 𝒜]
  [Ring ℬ] [StarRing ℬ] [Module ℂ ℬ]
variable [DecidableEq A]
omit [Fintype X] in
theorem _root_.solution (P : ProjectiveMeasurement X A 𝒜) (τ : TracialState 𝒜) (x : X)
    {a b : A} (hab : a ≠ b) : τ (P.M x a * P.M x b) = 0 := by
  have hnn : ∀ a', 0 ≤ τ (P.M x a' * P.M x b) := fun a' =>
    τ.nonneg_mul (P.selfAdjoint x a') (P.projective x a') (P.selfAdjoint x b)
      (P.projective x b)
  -- the total over `a'` is `τ (M^x_b)`, and the term `a' = b` alone already reaches it
  have hsum : ∑ a', τ (P.M x a' * P.M x b) = τ (P.M x b) := by
    rw [← map_sum, ← Finset.sum_mul, P.normalized, one_mul]
  have herase : ∑ a' ∈ Finset.univ.erase b, τ (P.M x a' * P.M x b) = 0 := by
    have h := Finset.sum_erase_add Finset.univ
      (fun a' => τ (P.M x a' * P.M x b)) (Finset.mem_univ b)
    rw [hsum, P.projective x b] at h
    linear_combination h
  exact (Finset.sum_eq_zero_iff_of_nonneg fun a' _ => hnn a').mp herase a
    (Finset.mem_erase.mpr ⟨hab, Finset.mem_univ a⟩)
end MIPRE.ProjectiveMeasurement
