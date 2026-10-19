-- Prove2me | solution 1 for MIPRE.re_eq_zero_of_tracialValue_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:45:11.223984+00:00
-- url     : https://prove2.me/submissions/eb21961e-49da-4d4b-938e-b3f8aed9b3ad

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/PerfectStrategy.lean (solution of MIPRE.re_eq_zero_of_tracialValue_eq_one);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_PerfectStrategy

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

namespace MIPRE.TracialState
section
open ComplexOrder Kronecker Matrix
open scoped MatrixOrder
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {𝒜 ℬ : Type*} [Ring 𝒜] [StarRing 𝒜] [Module ℂ 𝒜]
  [Ring ℬ] [StarRing ℬ] [Module ℂ ℬ]
/-- Real-part form of `TracialState.nonneg_mul`. -/
theorem re_nonneg_mul (τ : TracialState 𝒜) {p q : 𝒜} (hps : star p = p) (hpp : p * p = p)
    (hqs : star q = q) (hqq : q * q = q) : 0 ≤ (τ (p * q)).re := by
  simpa using (Complex.le_def.mp (τ.nonneg_mul hps hpp hqs hqq)).1
end
end MIPRE.TracialState

attribute [instance] MIPRE.CommutingStrategy.cstarAlgebra

namespace MIPRE
section
open Finset
open scoped ComplexOrder
variable {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A]
variable {𝒜 : Type*} [Ring 𝒜] [StarRing 𝒜] [Module ℂ 𝒜]
omit [Fintype X] [DecidableEq A] in
/-- At a fixed question pair the outcome probabilities sum to one: `∑_{a,b} τ(M^x_a M^y_b) =
τ(1) = 1`. -/
theorem sum_re_tracial (τ : TracialState 𝒜) (P : ProjectiveMeasurement X A 𝒜) (x y : X) :
    ∑ a, ∑ b, (τ (P.M x a * P.M y b)).re = 1 := by
  have hsum : ∑ a, ∑ b, τ (P.M x a * P.M y b) = 1 := by
    have h1 : ∀ a, ∑ b, τ (P.M x a * P.M y b) = τ (P.M x a) := fun a => by
      rw [← map_sum, ← Finset.mul_sum, P.normalized, mul_one]
    simp_rw [h1]
    rw [← map_sum, P.normalized, τ.map_one]
  have := congrArg Complex.re hsum
  simpa [Complex.re_sum] using this
end
end MIPRE

namespace MIPRE
section
open Finset
open scoped ComplexOrder
variable {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A]
variable {𝒜 : Type*} [Ring 𝒜] [StarRing 𝒜] [Module ℂ 𝒜]
omit [Fintype X] [DecidableEq A] in
/-- The outcome probabilities are nonnegative. -/
theorem re_nonneg_tracial (τ : TracialState 𝒜) (P : ProjectiveMeasurement X A 𝒜)
    (x y : X) (a b : A) : 0 ≤ (τ (P.M x a * P.M y b)).re :=
  τ.re_nonneg_mul (P.selfAdjoint x a) (P.projective x a) (P.selfAdjoint y b) (P.projective y b)
end
end MIPRE

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE
open Finset
open scoped ComplexOrder
variable {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A]
variable {𝒜 : Type*} [Ring 𝒜] [StarRing 𝒜] [Module ℂ 𝒜]
theorem _root_.solution (G : SynchronousGame X A) (τ : TracialState 𝒜)
    (P : ProjectiveMeasurement X A 𝒜) (h : tracialValue G τ P = 1)
    {x y : X} (hxy : 0 < G.μ x y) {a b : A} (hD : G.D x y a b = false) :
    (τ (P.M x a * P.M y b)).re = 0 := by
  classical
  have hle : ∀ p ∈ (univ : Finset (X × X × A × A)),
      G.μ p.1 p.2.1 * (if G.D p.1 p.2.1 p.2.2.1 p.2.2.2 then 1 else 0) *
          (τ (P.M p.1 p.2.2.1 * P.M p.2.1 p.2.2.2)).re
        ≤ G.μ p.1 p.2.1 * (τ (P.M p.1 p.2.2.1 * P.M p.2.1 p.2.2.2)).re := by
    intro p _
    cases hDp : G.D p.1 p.2.1 p.2.2.1 p.2.2.2 with
    | false => simpa using mul_nonneg (G.μ_nonneg _ _) (re_nonneg_tracial τ P _ _ _ _)
    | true => simp
  have hsumf : ∑ p : X × X × A × A,
      G.μ p.1 p.2.1 * (if G.D p.1 p.2.1 p.2.2.1 p.2.2.2 then 1 else 0) *
        (τ (P.M p.1 p.2.2.1 * P.M p.2.1 p.2.2.2)).re = 1 := by
    rw [← sum_flat (fun x y a b => G.μ x y * (if G.D x y a b then 1 else 0) *
      (τ (P.M x a * P.M y b)).re)]
    exact h
  have hsumg : ∑ p : X × X × A × A,
      G.μ p.1 p.2.1 * (τ (P.M p.1 p.2.2.1 * P.M p.2.1 p.2.2.2)).re = 1 := by
    rw [← sum_flat (fun x y a b => G.μ x y * (τ (P.M x a * P.M y b)).re)]
    refine (Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_).trans G.μ_sum_one
    simp_rw [← Finset.mul_sum]
    rw [sum_re_tracial τ P x y, mul_one]
  have hp := (Finset.sum_eq_sum_iff_of_le hle).mp (by rw [hsumf, hsumg]) (x, y, a, b)
    (mem_univ _)
  rw [hD] at hp
  simp only [Bool.false_eq_true, if_false, mul_zero, zero_mul] at hp
  exact (mul_eq_zero.mp hp.symm).resolve_left hxy.ne'
end MIPRE
