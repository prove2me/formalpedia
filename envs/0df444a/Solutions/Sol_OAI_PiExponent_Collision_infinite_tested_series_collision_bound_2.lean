-- Prove2me | solution 2 for OAI.PiExponent.Collision.infinite_tested_series_collision_bound
-- status  : ACCEPTED   (prove)
-- author  : @polylog
-- created : 2026-10-20T19:13:36.409122+00:00
-- url     : https://prove2.me/submissions/b9b19fd0-f259-486a-9e14-eb4f10148884

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Theorems.Thm_OAI_PiExponent_Collision_tested_series_determinant_limit
import Theorems.Thm_OAI_PiExponent_Collision_finite_tested_series_collision_bound

open scoped BigOperators Topology

/-- Infinite collision bound for tested series: the determinant of the limit matrix satisfies
the same collision bound as all of its truncations. -/
theorem solution
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (group : ι → κ) (B : ι → ℕ → ℂ) (C : κ → ℕ → ι → ℂ)
    (D s : ℝ) (L : ι → ℝ) (hD : 0 ≤ D) (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hL : ∀ r, 0 ≤ L r)
    (hC : ∀ A d c, ‖C A d c‖ ≤ D)
    (hB : ∀ r d, ‖B r d‖ ≤ L r * (s * s) ^ d)
    (T : Matrix ι ι ℂ)
    (hsum : ∀ r c, HasSum (fun d => B r d * C (group r) d c) (T r c)) :
    ‖T.det‖ ≤
      (((Fintype.card ι).factorial : ℝ) * D ^ Fintype.card ι * (∏ r, L r)) *
        s ^ (∑ A : κ, (((Finset.univ : Finset ι).filter
          (fun r => group r = A)).card.choose 2)) *
        ((1 - s)⁻¹) ^ Fintype.card ι := by
  apply OAI.PiExponent.Collision.tested_series_determinant_limit group B C T hsum
  intro N
  exact OAI.PiExponent.Collision.finite_tested_series_collision_bound group B C D s L N
    hD hs0 hs1 hL hC hB
