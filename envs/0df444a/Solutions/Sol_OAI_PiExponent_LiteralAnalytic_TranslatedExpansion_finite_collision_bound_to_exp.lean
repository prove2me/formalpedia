-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.finite_collision_bound_to_exp
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-20T17:38:19.409475+00:00
-- url     : https://prove2.me/submissions/67b1d39a-4784-47e6-be1f-b970b67b1eec

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_TranslatedExpansion_CollisionAnalyticHelpers
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_TranslatedExpansion_finite_collision_scalar_normalization

open scoped BigOperators Topology
open OAI.PiExponent
open OAI.PiExponent.Collision
open OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.CollisionAnalytic

theorem solution
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (group : ι → κ) (f : κ → ι → ℂ → ℂ)
    (center : ι → ℂ) (ell : ι → ℕ)
    {H budgetCoeff v : ℝ} (hH : 0 < H)
    (hell : ((∑ r, ell r : ℕ) : ℝ) ≤ (Fintype.card ι : ℝ) * H / v)
    (hfinite :
      ‖Matrix.det (fun r c => rowTest (ell r)
        (fun t => f (group r) c (center r + Complex.log (1 + t))))‖ ≤
        (((Fintype.card ι).factorial : ℝ) *
          Real.exp (H * budgetCoeff) ^ Fintype.card ι *
          (2 : ℝ) ^ (∑ r, ell r)) *
          Collision.collisionRatio ^
            (∑ A : κ, (((Finset.univ : Finset ι).filter
              (fun r => group r = A)).card.choose 2)) *
          ((1 - Collision.collisionRatio)⁻¹) ^ Fintype.card ι) :
      ‖Matrix.det (fun r c => rowTest (ell r)
        (fun t => f (group r) c (center r + Complex.log (1 + t))))‖ ≤
        Real.exp (-(Real.log 2 / 4) *
          (∑ A : κ,
            (((Finset.univ : Finset ι).filter (fun r => group r = A)).card : ℝ) ^ 2) +
          (Fintype.card ι : ℝ) * H *
            (budgetCoeff + Real.log 2 / v +
              Collision.collisionRemainder (Fintype.card ι) H)) := by
  have hscalar :=
    OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.finite_collision_scalar_normalization
      (budgetCoeff := budgetCoeff) group ell hH hell
  exact le_trans hfinite hscalar
