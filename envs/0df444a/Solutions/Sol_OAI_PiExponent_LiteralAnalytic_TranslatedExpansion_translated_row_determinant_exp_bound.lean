-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.translated_row_determinant_exp_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-20T13:01:12.196776+00:00
-- url     : https://prove2.me/submissions/e95da0e3-fe8b-42b4-94af-ac6bb5894465

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_TranslatedExpansion_CollisionAnalyticHelpers
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_TranslatedExpansion_translated_row_determinant_finite_collision_bound
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_TranslatedExpansion_finite_collision_bound_to_exp

open scoped BigOperators Topology
open OAI.PiExponent.Collision
open OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.CollisionAnalytic

theorem solution
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (group : ι → κ) (f : κ → ι → ℂ → ℂ)
    (center : ι → ℂ) (ell : ι → ℕ)
    (R : NNReal) (hR : 0 < R) {H budgetCoeff v : ℝ} (hH : 0 < H)
    (hf : ∀ A c, Differentiable ℂ (f A c))
    (hfD : ∀ A c z, z ∈ Metric.sphere (0 : ℂ) (R : ℝ) →
      ‖f A c z‖ ≤ Real.exp (H * budgetCoeff))
    (hc : ∀ r, ‖center r‖ + 3 / 4 ≤ (R : ℝ) / 2)
    (hell : ((∑ r, ell r : ℕ) : ℝ) ≤ (Fintype.card ι : ℝ) * H / v) :
    ‖Matrix.det (fun r c => rowTest (ell r)
      (fun t => f (group r) c (center r + Complex.log (1 + t))))‖ ≤
      Real.exp (-(Real.log 2 / 4) *
        (∑ A : κ,
          (((Finset.univ : Finset ι).filter (fun r => group r = A)).card : ℝ) ^ 2) +
        (Fintype.card ι : ℝ) * H *
          (budgetCoeff + Real.log 2 / v +
            OAI.PiExponent.Collision.collisionRemainder (Fintype.card ι) H)) := by
  have hfinite :=
    OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.translated_row_determinant_finite_collision_bound
      group f center ell R hR (H := H) (budgetCoeff := budgetCoeff) hf hfD hc
  exact OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.finite_collision_bound_to_exp
    group f center ell hH hell hfinite