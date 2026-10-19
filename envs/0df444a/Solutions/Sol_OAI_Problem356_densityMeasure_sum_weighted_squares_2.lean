-- Prove2me | solution 2 for OAI.Problem356.densityMeasure_sum_weighted_squares
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T21:08:04.609096+00:00
-- url     : https://prove2.me/submissions/4ded781e-e89a-42b5-9a2b-4948a41770c8

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/DisjointSquares.lean:L115-L136
-- (upload_full_project.md Phase 4): solution for node OAI.Problem356.densityMeasure_sum_weighted_squares. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CoulombCounterexample
import Definitions.Def_OAI_Analysis_CoulombTransport_AxisHessian
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchCoupling

-- ---- from OAI.Analysis.CoulombTransport.DisjointSquares ----
namespace OAI

universe uIndex uX

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Problem356

/-- The density assembled from weighted squares represents the corresponding
finite mixture of component measures. No disjointness is needed here. -/
theorem densityMeasure_sum_weighted_squares {ι : Type uIndex}
    (s : Finset ι) (a : ι → ℝ) (g : ι → E3 → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i)
    (hgm : ∀ i ∈ s, Measurable (g i)) :
    densityMeasure (fun x => ∑ i ∈ s, a i * (g i x) ^ 2) =
      ∑ i ∈ s, ENNReal.ofReal (a i) • densityMeasure (fun x => (g i x) ^ 2) := by
  have hpoint : ∀ x, ENNReal.ofReal (∑ i ∈ s, a i * (g i x) ^ 2) =
      ∑ i ∈ s, ENNReal.ofReal (a i) * ENNReal.ofReal ((g i x) ^ 2) := by
    intro x
    rw [ENNReal.ofReal_sum_of_nonneg (fun i hi => mul_nonneg (ha i hi) (sq_nonneg _))]
    exact Finset.sum_congr rfl (fun i hi => ENNReal.ofReal_mul (ha i hi))
  ext A hA
  simp only [Measure.finsetSum_apply, Measure.smul_apply, densityMeasure,
    withDensity_apply _ hA, smul_eq_mul]
  simp_rw [hpoint]
  rw [lintegral_finsetSum s (f := fun i x => ENNReal.ofReal (a i) * ENNReal.ofReal ((g i x) ^ 2))
    (fun i hi => measurable_const.mul ((hgm i hi).pow_const 2).ennreal_ofReal)]
  apply Finset.sum_congr rfl
  intro i hi
  exact lintegral_const_mul _ ((hgm i hi).pow_const 2).ennreal_ofReal

end Problem356

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem356
open MeasureTheory
open scoped BigOperators


theorem solution.{uIndex} : type_of% @_root_.OAI.Problem356.densityMeasure_sum_weighted_squares.{uIndex} := @_root_.OAI.Problem356.densityMeasure_sum_weighted_squares.{uIndex}
