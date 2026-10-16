-- Prove2me | solution 1 for MIPRE.tracialValue_le_one
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-15T19:58:27.501455+00:00
-- url     : https://prove2.me/submissions/74a956fe-e8be-4056-84a6-609ea93d5b49

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Games.lean (solution of MIPRE.tracialValue_le_one);
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
end MIPRE.TracialState

namespace MIPRE.TracialState
open ComplexOrder Kronecker Matrix
open scoped MatrixOrder
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {𝒜 ℬ : Type*} [Ring 𝒜] [StarRing 𝒜] [Module ℂ 𝒜]
  [Ring ℬ] [StarRing ℬ] [Module ℂ ℬ]
/-- Real-part form of `TracialState.nonneg_mul`. -/
theorem re_nonneg_mul (τ : TracialState 𝒜) {p q : 𝒜} (hps : star p = p) (hpp : p * p = p)
    (hqs : star q = q) (hqq : q * q = q) : 0 ≤ (τ (p * q)).re := by
  simpa using (Complex.le_def.mp (τ.nonneg_mul hps hpp hqs hqq)).1
end MIPRE.TracialState

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE
open ComplexOrder Kronecker Matrix
open scoped MatrixOrder
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {𝒜 ℬ : Type*} [Ring 𝒜] [StarRing 𝒜] [Module ℂ 𝒜]
  [Ring ℬ] [StarRing ℬ] [Module ℂ ℬ]
variable [DecidableEq A]
theorem _root_.solution (G : SynchronousGame X A) (τ : TracialState 𝒜)
    (P : ProjectiveMeasurement X A 𝒜) : tracialValue G τ P ≤ 1 := by
  have key : ∀ x y, ∑ a, ∑ b, (τ (P.M x a * P.M y b)).re = 1 := by
    intro x y
    have hsum : ∑ a, ∑ b, τ (P.M x a * P.M y b) = 1 := by
      have h1 : ∀ a, ∑ b, τ (P.M x a * P.M y b) = τ (P.M x a) := fun a => by
        rw [← map_sum, ← Finset.mul_sum, P.normalized, mul_one]
      simp_rw [h1]
      rw [← map_sum, P.normalized, τ.map_one]
    have := congrArg Complex.re hsum
    simpa [Complex.re_sum] using this
  calc tracialValue G τ P
      ≤ ∑ x, ∑ y, G.μ x y * ∑ a, ∑ b, (τ (P.M x a * P.M y b)).re := by
        refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun a _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun b _ => ?_
        have hre : 0 ≤ (τ (P.M x a * P.M y b)).re :=
          τ.re_nonneg_mul (P.selfAdjoint x a) (P.projective x a) (P.selfAdjoint y b)
            (P.projective y b)
        cases hD : G.D x y a b with
        | false => simpa [hD] using mul_nonneg (G.μ_nonneg x y) hre
        | true => simp
    _ = ∑ x, ∑ y, G.μ x y := by
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
        rw [key, mul_one]
    _ = 1 := G.μ_sum_one
end MIPRE
