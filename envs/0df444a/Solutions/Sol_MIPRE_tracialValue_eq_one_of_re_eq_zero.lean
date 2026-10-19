-- Prove2me | solution 1 for MIPRE.tracialValue_eq_one_of_re_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:45:11.847711+00:00
-- url     : https://prove2.me/submissions/18875696-16ed-48f4-b3f7-1d51067e71b3

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/PerfectStrategy.lean (solution of MIPRE.tracialValue_eq_one_of_re_eq_zero);
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

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE
open Finset
open scoped ComplexOrder
variable {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A]
variable {𝒜 : Type*} [Ring 𝒜] [StarRing 𝒜] [Module ℂ 𝒜]
theorem _root_.solution (G : SynchronousGame X A) (τ : TracialState 𝒜)
    (P : ProjectiveMeasurement X A 𝒜)
    (h : ∀ x y, 0 < G.μ x y → ∀ a b, G.D x y a b = false →
      (τ (P.M x a * P.M y b)).re = 0) :
    tracialValue G τ P = 1 := by
  classical
  have hterm : ∀ p : X × X × A × A,
      G.μ p.1 p.2.1 * (if G.D p.1 p.2.1 p.2.2.1 p.2.2.2 then 1 else 0) *
          (τ (P.M p.1 p.2.2.1 * P.M p.2.1 p.2.2.2)).re
        = G.μ p.1 p.2.1 * (τ (P.M p.1 p.2.2.1 * P.M p.2.1 p.2.2.2)).re := by
    intro p
    cases hD : G.D p.1 p.2.1 p.2.2.1 p.2.2.2 with
    | true => simp
    | false =>
        rcases (G.μ_nonneg p.1 p.2.1).lt_or_eq with hμ | hμ
        · rw [h _ _ hμ _ _ hD]; simp
        · rw [← hμ]; simp
  calc tracialValue G τ P
      = ∑ p : X × X × A × A, G.μ p.1 p.2.1 *
          (if G.D p.1 p.2.1 p.2.2.1 p.2.2.2 then 1 else 0) *
          (τ (P.M p.1 p.2.2.1 * P.M p.2.1 p.2.2.2)).re := by
        rw [← sum_flat (fun x y a b => G.μ x y * (if G.D x y a b then 1 else 0) *
          (τ (P.M x a * P.M y b)).re)]
        rfl
    _ = ∑ p : X × X × A × A, G.μ p.1 p.2.1 *
          (τ (P.M p.1 p.2.2.1 * P.M p.2.1 p.2.2.2)).re :=
        Finset.sum_congr rfl fun p _ => hterm p
    _ = 1 := by
        rw [← sum_flat (fun x y a b => G.μ x y * (τ (P.M x a * P.M y b)).re)]
        refine (Finset.sum_congr rfl fun x _ =>
          Finset.sum_congr rfl fun y _ => ?_).trans G.μ_sum_one
        simp_rw [← Finset.mul_sum]
        rw [sum_re_tracial τ P x y, mul_one]
end MIPRE
